/**
 * Who an execution is attributed to, and reentrancy, on chain: a real Safe
 * 1.4.1 with the v3 Roles (and a second Roles on the same Safe), against
 * hostile callers, targets and ERC-1271 signers.
 *
 * Deterministic cases:
 * - from inside an executed call, every execution entry point reverts with
 *   `Reentrancy`, also for an enabled member module; of all of Roles'
 *   state-changing functions only those keyed by the caller succeed there
 *   (`invalidate`, `renounceRole`);
 * - an ERC-1271 signer cannot execute from inside `isValidSignature` (a
 *   staticcall, during authentication);
 * - the signature parser: short signatures, the module list's sentinel,
 *   an EOA named as a contract signer, 65-byte contract signatures, replay,
 *   another Roles Modifier's digest, cancellation, a failed call with
 *   `shouldRevert` false or true;
 * - memberships: a batch is one use; a module that renounces during its
 *   own execution; a disabled module with a membership;
 * - nesting through another Roles Modifier on the same Safe.
 *
 * A stateful fuzz then runs random sequences of owner changes (grant,
 * revoke, default roles, enabling and disabling modules, allowances), time
 * jumps, renouncements, cancellations and executions (direct, by EOA and
 * contract modules; relayed with ECDSA, ERC-1271 in every mode, malformed,
 * replayed, tampered and cross-domain signatures; calls that succeed, fail,
 * re-enter, or are batches). A reference model predicts each outcome (the
 * exact error) and the state after it: allowance balance, consumed digests,
 * membership updates and uses, ether sent. `ATTRIBUTION_STEPS` (default 800),
 * `ATTRIBUTION_SEED`.
 */
import { expect } from "chai"
import {
  AbiCoder,
  Interface,
  ParamType,
  TypedDataEncoder,
  ZeroAddress,
  ZeroHash,
  concat,
  hexlify,
  randomBytes,
  recoverAddress,
  solidityPacked,
  toBeHex,
} from "ethers"
import type { Signer, TransactionReceipt } from "ethers"
import { network } from "hardhat"

import { iface as ifaceSafe } from "../eip712/setup/deploy-mastercopies/safeMastercopy.js"
import { deploySafe } from "../eip712/setup/safe.js"
import deployMastercopies from "../eip712/setup/deploy-mastercopies/index.js"

const connection = await network.create()
const { ethers } = connection
const abi = AbiCoder.defaultAbiCoder()

const STEPS = Number(process.env.ATTRIBUTION_STEPS ?? 800)
let seed = Number(process.env.ATTRIBUTION_SEED ?? 1)
const rnd = () => {
  seed = (seed * 1103515245 + 12345) % 2 ** 31
  return seed / 2 ** 31
}
const int = (n: number) => Math.floor(rnd() * n)
const pick = <T>(xs: readonly T[]): T => xs[int(xs.length)]
const chance = (p: number) => rnd() < p
const bump = (t: Record<string, number>, k: string) => {
  t[k] = (t[k] ?? 0) + 1
}

const Encoding = { None: 0, Static: 1, EtherValue: 6 } as const
const Operator = { Pass: 0, WithinAllowance: 28 } as const
const Options = { None: 0, Send: 1, DelegateCall: 2, Both: 3 }
const SENTINEL = "0x0000000000000000000000000000000000000001"
const multiSendIface = new Interface(["function multiSend(bytes transactions)"])
const randomKey = () => hexlify(randomBytes(32))
/** Enough gas for every call: with an estimated limit, a call that fails
 *  without reverting the transaction (`shouldRevert` false) can be given
 *  too little gas (see the gas case below). */
const G = { gasLimit: 15_000_000 }

const ROLE_TX = {
  RoleTx: [
    { name: "to", type: "address" },
    { name: "value", type: "uint256" },
    { name: "data", type: "bytes" },
    { name: "operation", type: "uint8" },
    { name: "roleKey", type: "bytes32" },
    { name: "shouldRevert", type: "bool" },
    { name: "salt", type: "bytes32" },
  ],
}
type RoleTx = {
  to: string
  value: bigint
  data: string
  operation: number
  roleKey: string
  shouldRevert: boolean
  salt: string
}

/* ------------------------------------------------------------------ setup */

async function deployRoles(owner: string, avatar: string) {
  const lib = async (name: string) =>
    (await (await ethers.getContractFactory(name)).deploy()).getAddress()
  const libraries = {
    ConditionStorer: await lib("ConditionStorer"),
    WithinRatioChecker: await lib("WithinRatioChecker"),
    CustomConditionChecker: await lib("CustomConditionChecker"),
  }
  const factory = await ethers.getContractFactory("Roles", { libraries })
  return factory.deploy(owner, avatar, avatar)
}

async function execSafe(owner: Signer, safe: string, to: string, data: string) {
  const approval = concat([
    abi.encode(["address"], [await owner.getAddress()]),
    ZeroHash,
    "0x01",
  ])
  await (
    await owner.sendTransaction({
      to: safe,
      data: ifaceSafe.encodeFunctionData("execTransaction", [
        to,
        0n,
        data,
        0,
        0n,
        0n,
        0n,
        ZeroAddress,
        ZeroAddress,
        approval,
      ]),
    })
  ).wait()
}

const encodeMultiSend = (txs: { to: string; value: bigint }[]) =>
  multiSendIface.encodeFunctionData("multiSend", [
    concat(
      txs.map((t) =>
        solidityPacked(
          ["uint8", "address", "uint256", "uint256", "bytes"],
          [0, t.to, t.value, 0, "0x"]
        )
      )
    ),
  ])

/** Everything the cases share. */
async function world() {
  await deployMastercopies(ethers)
  const [ownerA, e1, e2, x, relayer] = await ethers.getSigners()
  const safe = await deploySafe(
    {
      owners: [await ownerA.getAddress()],
      threshold: 1,
      creationNonce: BigInt(randomKey()),
    },
    ownerA as any
  )
  const R = await deployRoles(await ownerA.getAddress(), safe)
  const R2 = await deployRoles(await ownerA.getAddress(), safe)
  for (const r of [R, R2])
    await execSafe(
      ownerA,
      safe,
      safe,
      ifaceSafe.encodeFunctionData("enableModule", [await r.getAddress()])
    )
  await (
    await ownerA.sendTransaction({ to: safe, value: ethers.parseEther("10") })
  ).wait()

  const H = await (await ethers.getContractFactory("Hostile")).deploy()
  const S = await (await ethers.getContractFactory("Signer1271")).deploy()
  const Rev = await (await ethers.getContractFactory("Reverter")).deploy()
  const multiSend = await (
    await ethers.getContractFactory("MultiSend")
  ).deploy()
  const unwrapper = await (
    await ethers.getContractFactory("MultiSendUnwrapper")
  ).deploy()
  const okT = ethers.Wallet.createRandom().address
  const K1 = randomKey()
  const role1 = randomKey()
  const role2 = randomKey()

  const addr = {
    H: await H.getAddress(),
    S: await S.getAddress(),
    Rev: await Rev.getAddress(),
    multiSend: await multiSend.getAddress(),
    R: await R.getAddress(),
    R2: await R2.getAddress(),
    e1: await e1.getAddress(),
    e2: await e2.getAddress(),
    x: await x.getAddress(),
  }

  for (const r of [R, R2]) {
    const o = r.connect(ownerA)
    await o.setTransactionUnwrapper(
      addr.multiSend,
      multiSendIface.getFunction("multiSend")!.selector,
      await unwrapper.getAddress()
    )
    await o.setAllowance(K1, 1000, 0, 0, 0, 0)
    // role 1: ether to okT within K1, the hostile target, the reverter,
    // batches (MultiSend is unwrapped, its entries are checked)
    for (const t of [okT, addr.H, addr.Rev]) await o.scopeTarget(role1, t)
    await o.allowTarget(
      role1,
      okT,
      [
        {
          parent: 0,
          paramType: Encoding.EtherValue,
          operator: Operator.WithinAllowance,
          compValue: K1,
        },
      ],
      Options.Send
    )
    await o.allowTarget(role1, addr.H, [], Options.None)
    await o.allowTarget(role1, addr.Rev, [], Options.None)
    // role 2: okT without ether
    await o.scopeTarget(role2, okT)
    await o.allowTarget(role2, okT, [], Options.None)
  }

  const chainId = (await ethers.provider.getNetwork()).chainId
  const digest = (r: string, m: RoleTx) =>
    TypedDataEncoder.hash({ chainId, verifyingContract: r }, ROLE_TX, m)
  const sign = (s: Signer, r: string, m: RoleTx) =>
    s.signTypedData({ chainId, verifyingContract: r }, ROLE_TX, m)

  return {
    ownerA,
    e1,
    e2,
    x,
    relayer,
    safe,
    R,
    R2,
    H,
    S,
    okT,
    K1,
    role1,
    role2,
    addr,
    digest,
    sign,
  }
}

type World = Awaited<ReturnType<typeof world>>

const errorName = (w: World, e: any): string => {
  const data = e?.data ?? e?.error?.data ?? e?.info?.error?.data
  if (typeof data === "string" && data.length >= 10) {
    const parsed = w.R.interface.parseError(data)
    if (parsed) return parsed.name
    return data.slice(0, 10)
  }
  return `unparsed: ${e?.shortMessage ?? e?.message ?? e}`
}

/** The outcome of a transaction: "ok" / "false" (the avatar's call failed,
 *  `shouldRevert` false) or the custom error. */
async function outcome(
  w: World,
  send: () => Promise<any>
): Promise<{ result: string; receipt?: TransactionReceipt }> {
  try {
    const tx = await send()
    const receipt: TransactionReceipt = await tx.wait()
    const safeIface = new Interface([
      "event ExecutionFromModuleSuccess(address indexed module)",
      "event ExecutionFromModuleFailure(address indexed module)",
    ])
    let result = "ok"
    for (const l of receipt.logs) {
      if (l.address.toLowerCase() !== w.safe.toLowerCase()) continue
      const p = safeIface.parseLog(l)
      if (p?.name === "ExecutionFromModuleFailure") result = "false"
    }
    return { result, receipt }
  } catch (e) {
    return { result: errorName(w, e) }
  }
}

const sel = (w: World, name: string) => w.R.interface.getError(name)!.selector

/** The calls the hostile target makes into Roles while it is being called:
 *  all four execution entry points, as a module with a valid membership. */
async function reentryPlan(w: World) {
  const R = w.R.interface
  const m: RoleTx = {
    to: w.okT,
    value: 0n,
    data: "0x",
    operation: 0,
    roleKey: w.role1,
    shouldRevert: false,
    salt: randomKey(),
  }
  const sig = concat([w.addr.S, hexlify(randomBytes(10))])
  return [
    R.encodeFunctionData("execTransactionWithRole", [
      w.okT,
      0,
      "0x",
      0,
      w.role1,
      false,
    ]),
    R.encodeFunctionData("execTransactionFromModule", [w.okT, 0, "0x", 0]),
    R.encodeFunctionData("execTransactionFromModuleReturnData", [
      w.okT,
      0,
      "0x",
      0,
    ]),
    R.encodeFunctionData("execTransactionWithSignature", [
      m.to,
      m.value,
      m.data,
      m.operation,
      m.roleKey,
      m.shouldRevert,
      m.salt,
      sig,
    ]),
  ]
}

/** A default argument of each type, for calling any function. */
function defaultArg(t: ParamType, w: World): any {
  if (t.baseType === "array")
    return t.arrayLength && t.arrayLength > 0
      ? Array.from({ length: t.arrayLength }, () =>
          defaultArg(t.arrayChildren!, w)
        )
      : []
  if (t.baseType === "tuple") return t.components!.map((c) => defaultArg(c, w))
  if (t.type === "address") return w.addr.H
  if (t.type === "bool") return false
  if (t.type === "bytes") return "0x"
  if (t.type === "string") return ""
  if (t.type.startsWith("bytes"))
    return w.role1.slice(0, 2 + 2 * Number(t.type.slice(5)))
  return 0
}

/* ------------------------------------------------------------ deterministic */

describe("attribution and reentrancy, end to end", () => {
  after(async () => {
    await connection.close()
  })

  it("from inside an executed call, every execution entry point reverts with Reentrancy", async () => {
    const w = await world()
    const { R, H, S, ownerA, role1, addr } = w
    // H and S are enabled members of role 1, H's default role is role 1
    await R.connect(ownerA).grantRole(addr.H, role1, 0, 0, 0)
    await R.connect(ownerA).grantRole(addr.S, role1, 0, 0, 0)
    await R.connect(ownerA).setDefaultRole(addr.H, role1)
    await S.setMode(1)
    const plan = await reentryPlan(w)

    // at the top level, each of these executes
    for (const data of plan) {
      const r = await outcome(w, () => H.act(addr.R, data))
      expect(r.result).to.equal("ok")
    }
    // from inside an execution (the avatar calls H), each reverts
    await H.setPlan(
      plan.map(() => addr.R),
      plan,
      false
    )
    const r = await outcome(w, () =>
      H.act(
        addr.R,
        R.interface.encodeFunctionData("execTransactionWithRole", [
          addr.H,
          0,
          "0x12345678",
          0,
          role1,
          true,
        ])
      )
    )
    expect(r.result).to.equal("ok")
    const results = await Promise.all(plan.map((_, i) => H.results(i)))
    expect(results).to.deep.equal(plan.map(() => sel(w, "Reentrancy")))
  })

  it("from inside an executed call, only Roles functions keyed by the caller succeed", async () => {
    const w = await world()
    const { R, H, ownerA, role1, addr } = w
    await R.connect(ownerA).grantRole(addr.H, role1, 0, 0, 0)
    const fns = R.interface.fragments.filter(
      (f: any) =>
        f.type === "function" && !["view", "pure"].includes(f.stateMutability)
    ) as any[]
    const datas = fns.map((f) =>
      R.interface.encodeFunctionData(
        f,
        f.inputs.map((i: ParamType) => defaultArg(i, w))
      )
    )
    await H.setPlan(
      datas.map(() => addr.R),
      datas,
      false
    )
    await R.connect(ownerA).grantRole(addr.e1, role1, 0, 0, 0)
    const r2 = await outcome(w, () =>
      R.connect(w.e1).execTransactionWithRole(
        addr.H,
        0,
        "0x12345678",
        0,
        role1,
        true
      )
    )
    expect(r2.result).to.equal("ok")

    const table: Record<string, string> = {}
    for (const [i, f] of fns.entries()) {
      const s = await H.results(i)
      table[f.name] =
        s === "0x00000000" ? "ok" : (R.interface.getError(s)?.name ?? s)
    }
    const succeeded = Object.keys(table).filter((k) => table[k] === "ok")
    expect(succeeded.sort()).to.deep.equal(["invalidate", "renounceRole"])
    for (const f of [
      "execTransactionFromModule",
      "execTransactionFromModuleReturnData",
      "execTransactionWithRole",
      "execTransactionWithSignature",
    ])
      expect(table[f]).to.equal("Reentrancy")
    console.log(
      `      ${fns.length} state-changing functions: ` +
        Object.entries(
          Object.values(table).reduce(
            (t, v) => ((t[v] = (t[v] ?? 0) + 1), t),
            {} as Record<string, number>
          )
        )
          .map(([k, n]) => `${k} ${n}`)
          .join(", ")
    )
  })

  it("an ERC-1271 signer cannot execute from inside isValidSignature", async () => {
    const w = await world()
    const { R, S, ownerA, role1, addr, relayer, okT } = w
    await R.connect(ownerA).grantRole(addr.S, role1, 0, 0, 0)
    // inside the check, S tries a direct execution (as a member module)
    await S.setReenter(
      addr.R,
      R.interface.encodeFunctionData("execTransactionWithRole", [
        okT,
        0,
        "0x",
        0,
        role1,
        false,
      ])
    )
    await S.setMode(4)
    const m: RoleTx = {
      to: okT,
      value: 7n,
      data: "0x",
      operation: 0,
      roleKey: role1,
      shouldRevert: true,
      salt: randomKey(),
    }
    const sig = concat([addr.S, "0xabcdef"])
    const before = await ethers.provider.getBalance(okT)
    const r = await outcome(w, () =>
      R.connect(relayer).execTransactionWithSignature(
        m.to,
        m.value,
        m.data,
        m.operation,
        m.roleKey,
        m.shouldRevert,
        m.salt,
        sig
      )
    )
    // mode 4 answers valid only if the reentry failed
    expect(r.result).to.equal("ok")
    expect(await ethers.provider.getBalance(okT)).to.equal(before + 7n)
    expect(await R.consumed(addr.S, w.digest(addr.R, m))).to.equal(true)
  })

  it("the signature parser and replay protection", async () => {
    const w = await world()
    const { R, R2, S, ownerA, e1, x, role1, addr, relayer, okT } = w
    await R.connect(ownerA).grantRole(addr.e1, role1, 0, 0, 0)
    await R.connect(ownerA).grantRole(addr.S, role1, 0, 0, 0)
    await R2.connect(ownerA).grantRole(addr.e1, role1, 0, 0, 0)
    const tx = (over: Partial<RoleTx> = {}): RoleTx => ({
      to: okT,
      value: 1n,
      data: "0x",
      operation: 0,
      roleKey: role1,
      shouldRevert: true,
      salt: randomKey(),
      ...over,
    })
    const relay = (r: any, m: RoleTx, sig: string) =>
      outcome(w, () =>
        r
          .connect(relayer)
          .execTransactionWithSignature(
            m.to,
            m.value,
            m.data,
            m.operation,
            m.roleKey,
            m.shouldRevert,
            m.salt,
            sig
          )
      )

    // too short: no signer
    expect((await relay(R, tx(), "0x" + "11".repeat(19))).result).to.equal(
      "NotAuthorized"
    )
    // the module list's sentinel (address 1, a precompile without code)
    await S.setMode(1)
    expect((await relay(R, tx(), concat([SENTINEL, "0x00"]))).result).to.equal(
      "NotAuthorized"
    )
    // an EOA module named as a contract signer: no code, not valid
    expect((await relay(R, tx(), concat([addr.e1, "0x00"]))).result).to.equal(
      "NotAuthorized"
    )
    // a non-module's valid ECDSA signature
    const mx = tx()
    expect((await relay(R, mx, await w.sign(x, addr.R, mx))).result).to.equal(
      "NotAuthorized"
    )
    // a module's signature for another Roles Modifier
    const m2 = tx()
    expect((await relay(R, m2, await w.sign(e1, addr.R2, m2))).result).to.equal(
      "NotAuthorized"
    )
    // a tampered field
    const mt = tx()
    expect(
      (await relay(R, { ...mt, value: 2n }, await w.sign(e1, addr.R, mt)))
        .result
    ).to.equal("NotAuthorized")
    // valid once, then consumed
    const m = tx()
    const sig = await w.sign(e1, addr.R, m)
    expect((await relay(R, m, sig)).result).to.equal("ok")
    expect((await relay(R, m, sig)).result).to.equal("HashAlreadyConsumed")
    // malleated (high s): ecrecover gives another address
    // cancelled before use
    const mc = tx()
    await R.connect(e1).invalidate(w.digest(addr.R, mc))
    expect((await relay(R, mc, await w.sign(e1, addr.R, mc))).result).to.equal(
      "HashAlreadyConsumed"
    )

    // a 65-byte contract signature (20 + 45 bytes) is tried as ECDSA first:
    // if that recovers an address, it is the signer (here not a module), and
    // the contract's valid signature is rejected; if recovery fails (here
    // `v` = 0) it is checked by ERC-1271
    const m65 = tx()
    const d65 = w.digest(addr.R, m65)
    let recovering: string | undefined
    while (!recovering) {
      // r starts with the signer's address; a small s; v = 27
      const sig = concat([
        addr.S,
        hexlify(randomBytes(12)),
        "0x00",
        hexlify(randomBytes(31)),
        "0x1b",
      ])
      try {
        recoverAddress(d65, sig)
        recovering = sig
      } catch {}
    }
    expect((await relay(R, m65, recovering)).result).to.equal("NotAuthorized")
    expect(
      (await relay(R, m65, concat([recovering.slice(0, 2 + 64 * 2), "0x00"])))
        .result
    ).to.equal("ok")

    // a failed call with shouldRevert false: the digest is used up, nothing
    // else changes; with shouldRevert true: everything reverts
    const fail = tx({ to: addr.Rev, value: 0n, shouldRevert: false })
    await R.connect(ownerA).scopeTarget(role1, addr.Rev)
    await R.connect(ownerA).allowTarget(role1, addr.Rev, [], Options.None)
    const fsig = await w.sign(e1, addr.R, fail)
    expect((await relay(R, fail, fsig)).result).to.equal("false")
    expect(await R.consumed(addr.e1, w.digest(addr.R, fail))).to.equal(true)
    const failR = tx({ to: addr.Rev, value: 0n, shouldRevert: true })
    expect(
      (await relay(R, failR, await w.sign(e1, addr.R, failR))).result
    ).to.equal("ModuleTransactionFailed")
    expect(await R.consumed(addr.e1, w.digest(addr.R, failR))).to.equal(false)
  })

  it("with shouldRevert false, the gas limit decides whether a relayed call runs; the signature is used either way", async () => {
    const w = await world()
    const { R, H, ownerA, e1, role1, addr, relayer } = w
    await R.connect(ownerA).grantRole(addr.e1, role1, 0, 0, 0)
    // the call to H costs some gas: H tries the four entry points
    const plan = await reentryPlan(w)
    await H.setPlan(
      plan.map(() => addr.R),
      plan,
      false
    )
    const relayWithGas = async (shouldRevert: boolean, gasLimit: number) => {
      const m: RoleTx = {
        to: addr.H,
        value: 0n,
        data: "0x12345678",
        operation: 0,
        roleKey: role1,
        shouldRevert,
        salt: randomKey(),
      }
      const sig = await w.sign(e1, addr.R, m)
      const runs = await H.runs()
      const r = await outcome(w, () =>
        R.connect(relayer).execTransactionWithSignature(
          m.to,
          m.value,
          m.data,
          m.operation,
          m.roleKey,
          m.shouldRevert,
          m.salt,
          sig,
          { gasLimit }
        )
      )
      return {
        result: r.result,
        ran: (await H.runs()) > runs,
        consumed: await R.consumed(addr.e1, w.digest(addr.R, m)),
      }
    }
    /** The outcome at the lowest gas limit (in steps of 2000) at which the
     *  transaction does not revert. */
    const lowest = async (shouldRevert: boolean) => {
      for (let g = 40_000; g < 3_000_000; g += 2_000) {
        const r = await relayWithGas(shouldRevert, g)
        if (r.result === "ok" || r.result === "false") return { ...r, gas: g }
      }
      throw new Error("no gas limit worked")
    }
    // shouldRevert false: the relayer can pick a limit at which the call
    // fails for lack of gas, and the signature is used up
    const f = await lowest(false)
    expect(f).to.include({ result: "false", ran: false, consumed: true })
    // shouldRevert true: either the call runs or nothing happens
    const t = await lowest(true)
    expect(t).to.include({ result: "ok", ran: true, consumed: true })
    console.log(
      `      lowest gas limits: ${f.gas} (call fails, signature used), ${t.gas} (call runs)`
    )
  })

  it("memberships: a batch is one use, renouncing during the own execution, disabled modules", async () => {
    const w = await world()
    const { R, H, ownerA, e1, role1, addr, okT } = w
    const usesOf = (rc?: TransactionReceipt) =>
      (rc?.logs ?? [])
        .map((l) => {
          try {
            return R.interface.parseLog(l)
          } catch {
            return null
          }
        })
        .filter((p) => p && ["UpdateRole", "RevokeRole"].includes(p.name))
        .map((p) =>
          p!.name === "RevokeRole" ? "revoked" : p!.args[4].toString()
        )

    // a batch of three entries uses one of three uses
    await R.connect(ownerA).grantRole(addr.e1, role1, 0, 0, 3)
    const batch = encodeMultiSend([
      { to: okT, value: 1n },
      { to: okT, value: 2n },
      { to: okT, value: 3n },
    ])
    const b = await outcome(w, () =>
      R.connect(e1).execTransactionWithRole(
        addr.multiSend,
        0,
        batch,
        1,
        role1,
        true
      )
    )
    expect(b.result).to.equal("ok")
    expect(usesOf(b.receipt)).to.deep.equal(["2"])

    // H renounces role 1 while executing with it (the first event): with
    // limited uses, settlement writes the membership back (uses - 1)
    await R.connect(ownerA).grantRole(addr.H, role1, 0, 0, 5)
    const renounce = R.interface.encodeFunctionData("renounceRole", [role1])
    await H.setPlan([addr.R], [renounce], false)
    const call = R.interface.encodeFunctionData("execTransactionWithRole", [
      addr.H,
      0,
      "0x12345678",
      0,
      role1,
      true,
    ])
    const r1 = await outcome(w, () => H.act(addr.R, call))
    expect(r1.result).to.equal("ok")
    expect(await H.results(0)).to.equal("0x00000000")
    expect(usesOf(r1.receipt)).to.deep.equal(["revoked", "4"])
    expect(await R.isMember(role1, addr.H)).to.equal(true)
    // with unlimited uses settlement writes nothing: the renouncement stays
    await R.connect(ownerA).grantRole(addr.H, role1, 0, 0, 0)
    const r2 = await outcome(w, () => H.act(addr.R, call))
    expect(r2.result).to.equal("ok")
    expect(usesOf(r2.receipt)).to.deep.equal(["revoked"])
    expect(await R.isMember(role1, addr.H)).to.equal(false)

    // a module disabled after the grant cannot execute, directly or signed
    await R.connect(ownerA).grantRole(addr.e1, role1, 0, 0, 0)
    const [mods] = await R.getModulesPaginated(SENTINEL, 100)
    const i = mods.findIndex(
      (m: string) => m.toLowerCase() === addr.e1.toLowerCase()
    )
    await R.connect(ownerA).disableModule(
      i === 0 ? SENTINEL : mods[i - 1],
      addr.e1
    )
    expect(await R.isMember(role1, addr.e1)).to.equal(true)
    expect(
      (
        await outcome(w, () =>
          R.connect(e1).execTransactionWithRole(okT, 0, "0x", 0, role1, true)
        )
      ).result
    ).to.equal("NotAuthorized")
    const m: RoleTx = {
      to: okT,
      value: 0n,
      data: "0x",
      operation: 0,
      roleKey: role1,
      shouldRevert: true,
      salt: randomKey(),
    }
    const sig = await w.sign(e1, addr.R, m)
    expect(
      (
        await outcome(w, () =>
          R.connect(w.relayer).execTransactionWithSignature(
            m.to,
            m.value,
            m.data,
            m.operation,
            m.roleKey,
            m.shouldRevert,
            m.salt,
            sig
          )
        )
      ).result
    ).to.equal("NotAuthorized")
  })

  it("an execution can nest an execution through another Roles Modifier on the same Safe", async () => {
    const w = await world()
    const { R, R2, H, ownerA, e1, role1, addr, okT, K1 } = w
    await R.connect(ownerA).grantRole(addr.e1, role1, 0, 0, 0)
    await R2.connect(ownerA).grantRole(addr.H, role1, 0, 0, 0)
    // inside e1's execution through R, H executes through R2
    const inner = R2.interface.encodeFunctionData("execTransactionWithRole", [
      okT,
      5,
      "0x",
      0,
      role1,
      true,
    ])
    await H.setPlan([addr.R2], [inner], false)
    const r = await outcome(w, () =>
      R.connect(e1).execTransactionWithRole(
        addr.H,
        0,
        "0x12345678",
        0,
        role1,
        true
      )
    )
    expect(r.result).to.equal("ok")
    expect(await H.results(0)).to.equal("0x00000000")
    // each Roles guards only itself, and settles its own allowance
    expect((await R2.allowances(K1)).balance).to.equal(995n)
    expect((await R.allowances(K1)).balance).to.equal(1000n)
  })

  /* ------------------------------------------------------------ the fuzz */

  it(`a reference model predicts every outcome (${STEPS} random steps)`, async () => {
    const w = await world()
    const { R, H, S, ownerA, e1, e2, x, relayer, role1, role2, addr, okT, K1 } =
      w
    const provider = ethers.provider

    type Mem = { start: bigint; end: bigint; uses: bigint | "inf" }
    const MODULES = ["e1", "e2", "H", "S"] as const
    type Mod = (typeof MODULES)[number]
    const modAddr = (m: Mod) => addr[m]
    const ROLES = [role1, role2, ZeroHash]
    const EXEC_ROLES = [role1, role1, role1, role2, role2, ZeroHash]

    await H.setPlan(
      (await reentryPlan(w)).map(() => addr.R),
      await reentryPlan(w),
      false
    )

    const model = {
      now: BigInt((await provider.getBlock("latest"))!.timestamp),
      enabled: new Set<string>(),
      members: new Map<string, Mem>(),
      defaults: new Map<string, string>(),
      allowance: 1000n,
      consumed: new Set<string>(),
      approved: new Set<string>(),
      mode: 0,
    }
    const memKey = (role: string, m: string) => `${role}:${m.toLowerCase()}`
    const digests: { signer: string; digest: string }[] = []
    const used: { m: RoleTx; sig: string; signer: string }[] = []
    const tally: Record<string, number> = {}
    /** Whether S accepts a digest now. */
    const validS = (d: string) =>
      model.mode === 1 ||
      model.mode === 4 ||
      (model.mode === 0 && model.approved.has(d))

    // a timestamp for every transaction, so predictions are exact
    const at = async <T>(f: () => Promise<T>): Promise<T> => {
      model.now += 1n
      await provider.send("evm_setNextBlockTimestamp", [toBeHex(model.now)])
      return f()
    }
    const asModule = (m: Mod, data: string) =>
      m === "e1"
        ? e1.sendTransaction({ to: addr.R, data, ...G })
        : m === "e2"
          ? e2.sendTransaction({ to: addr.R, data, ...G })
          : m === "H"
            ? H.act(addr.R, data, G)
            : S.act(addr.R, data, G)

    type Call = {
      kind: string
      to: string
      value: bigint
      data: string
      operation: number
      entries?: bigint[]
    }
    const randomCall = (): Call => {
      const r = int(10)
      if (r < 4)
        return {
          kind: "send",
          to: okT,
          value: BigInt(int(300)),
          data: "0x",
          operation: 0,
        }
      if (r < 5)
        return {
          kind: "revert",
          to: addr.Rev,
          value: 0n,
          data: "0x12345678",
          operation: 0,
        }
      if (r < 7)
        return {
          kind: "reenter",
          to: addr.H,
          value: 0n,
          data: "0x12345678",
          operation: 0,
        }
      if (r < 9) {
        const entries = Array.from({ length: 1 + int(3) }, () =>
          BigInt(int(200))
        )
        return {
          kind: "batch",
          to: addr.multiSend,
          value: 0n,
          data: encodeMultiSend(entries.map((v) => ({ to: okT, value: v }))),
          operation: 1,
          entries,
        }
      }
      return {
        kind: "denied",
        to: x.address,
        value: 0n,
        data: "0x",
        operation: 0,
      }
    }

    /** What `_authenticate` + `_authorize` + the call do, from the model. */
    const predictExec = (
      module: string,
      role: string,
      c: Call,
      shouldRevert: boolean
    ) => {
      if (role === ZeroHash) return { error: "NoMembership" }
      const mem = model.members.get(memKey(role, module))
      if (!mem) return { error: "NoMembership" }
      if (model.now < mem.start) return { error: "MembershipNotYetValid" }
      if (model.now > mem.end) return { error: "MembershipExpired" }
      let charge = 0n
      const entries =
        c.kind === "batch"
          ? c.entries!.map((v) => ({ to: okT, value: v }))
          : [{ to: c.to, value: c.value }]
      for (const e of entries) {
        if (role === role1) {
          if (e.to === okT) {
            if (charge + e.value > model.allowance)
              return { error: "ConditionViolation" }
            charge += e.value
          } else if (e.to !== addr.H && e.to !== addr.Rev)
            return { error: "TransactionNotAllowed" }
        } else {
          if (e.to !== okT) return { error: "TransactionNotAllowed" }
          if (e.value > 0n) return { error: "SendNotAllowed" }
        }
      }
      const success = c.kind !== "revert"
      if (!success && shouldRevert) return { error: "ModuleTransactionFailed" }
      return { success, charge, mem }
    }

    const check = async (
      label: string,
      predicted: {
        error?: string
        success?: boolean
        charge?: bigint
        mem?: Mem
      },
      r: { result: string; receipt?: TransactionReceipt },
      module: string,
      role: string,
      c: Call,
      sentBefore: bigint
    ) => {
      const want = predicted.error ?? (predicted.success ? "ok" : "false")
      expect(r.result, `${label}: outcome`).to.equal(want)
      bump(tally, `${label} ${want}`)
      const ok = want === "ok"
      if (ok) {
        model.allowance -= predicted.charge!
        const mem = predicted.mem!
        const events = (r.receipt!.logs ?? [])
          .filter((l) => l.address.toLowerCase() === addr.R.toLowerCase())
          .map((l) => R.interface.parseLog(l))
          .filter((p) => p && ["UpdateRole", "RevokeRole"].includes(p.name))
          .map((p) =>
            p!.name === "RevokeRole" ? "revoked" : p!.args[4].toString()
          )
        if (mem.uses === "inf")
          expect(events, `${label}: membership`).to.deep.equal([])
        else if (mem.uses <= 1n) {
          expect(events, `${label}: membership`).to.deep.equal(["revoked"])
          model.members.delete(memKey(role, module))
        } else {
          expect(events, `${label}: membership`).to.deep.equal([
            (mem.uses - 1n).toString(),
          ])
          mem.uses -= 1n
        }
        if (c.kind === "reenter") {
          const n = Number(await H.resultCount())
          for (let i = 0; i < n; i++)
            expect(await H.results(i), `${label}: reentry`).to.equal(
              sel(w, "Reentrancy")
            )
          bump(tally, "reentries refused")
        }
      }
      const sent =
        ok && (c.kind === "send" || c.kind === "batch")
          ? c.kind === "send"
            ? c.value
            : c.entries!.reduce((a, b) => a + b, 0n)
          : 0n
      expect(await provider.getBalance(okT), `${label}: ether sent`).to.equal(
        sentBefore + sent
      )
      expect((await R.allowances(K1)).balance, `${label}: allowance`).to.equal(
        model.allowance
      )
    }

    // start with every module an unlimited member of both roles
    for (const m of MODULES)
      for (const role of [role1, role2]) {
        await at(() => R.connect(ownerA).grantRole(modAddr(m), role, 0, 0, 0))
        model.members.set(memKey(role, modAddr(m)), {
          start: 0n,
          end: 2n ** 64n - 1n,
          uses: "inf",
        })
        model.enabled.add(modAddr(m).toLowerCase())
      }
    for (const m of MODULES) {
      await at(() => R.connect(ownerA).setDefaultRole(modAddr(m), role1))
      model.defaults.set(modAddr(m).toLowerCase(), role1)
    }

    for (let step = 0; step < STEPS; step++) {
      const a = int(100)
      const sentBefore = await provider.getBalance(okT)

      if (a < 12) {
        // owner grants a membership (and enables the module)
        const m = pick(MODULES)
        const role = pick([role1, role2])
        const start = chance(0.8) ? 0n : model.now + BigInt(int(2000)) - 500n
        const end = chance(0.6) ? 0n : model.now + BigInt(int(4000))
        const uses = chance(0.5) ? 0n : BigInt(1 + int(4))
        await at(() =>
          R.connect(ownerA).grantRole(
            modAddr(m),
            role,
            start < 0n ? 0n : start,
            end,
            uses
          )
        )
        model.members.set(memKey(role, modAddr(m)), {
          start: start < 0n ? 0n : start,
          end: end === 0n ? 2n ** 64n - 1n : end,
          uses: uses === 0n ? "inf" : uses,
        })
        model.enabled.add(modAddr(m).toLowerCase())
        bump(tally, "grant")
      } else if (a < 14) {
        const m = pick(MODULES)
        const role = pick([role1, role2])
        await at(() => R.connect(ownerA).revokeRole(modAddr(m), role))
        model.members.delete(memKey(role, modAddr(m)))
        bump(tally, "revoke")
      } else if (a < 15) {
        // a module renounces
        const m = pick(MODULES)
        const role = pick([role1, role2])
        await at(() =>
          asModule(m, R.interface.encodeFunctionData("renounceRole", [role]))
        )
        model.members.delete(memKey(role, modAddr(m)))
        bump(tally, "renounce")
      } else if (a < 18) {
        // owner disables or enables a module
        const m = pick(MODULES)
        const a_ = modAddr(m)
        if (model.enabled.has(a_.toLowerCase()) && chance(0.4)) {
          const [mods] = await R.getModulesPaginated(SENTINEL, 100)
          const i = mods.findIndex(
            (x: string) => x.toLowerCase() === a_.toLowerCase()
          )
          await at(() =>
            R.connect(ownerA).disableModule(
              i === 0 ? SENTINEL : mods[i - 1],
              a_
            )
          )
          model.enabled.delete(a_.toLowerCase())
          bump(tally, "disable")
        } else if (!model.enabled.has(a_.toLowerCase())) {
          await at(() => R.connect(ownerA).enableModule(a_))
          model.enabled.add(a_.toLowerCase())
          bump(tally, "enable")
        }
      } else if (a < 20) {
        const m = pick(MODULES)
        const role = pick(ROLES)
        await at(() => R.connect(ownerA).setDefaultRole(modAddr(m), role))
        model.defaults.set(modAddr(m).toLowerCase(), role)
        bump(tally, "default role")
      } else if (a < 23) {
        model.now += BigInt(pick([10, 600, 3000]))
        bump(tally, "time")
      } else if (a < 25) {
        const b = BigInt(int(1000))
        await at(() => R.connect(ownerA).setAllowance(K1, b, 0, 0, 0, 0))
        model.allowance = b
        bump(tally, "set allowance")
      } else if (a < 27) {
        model.mode = pick([0, 0, 1, 2, 3, 4, 5])
        await at(() => S.setMode(model.mode))
        if (model.mode === 4)
          await at(() =>
            S.setReenter(
              addr.R,
              R.interface.encodeFunctionData("execTransactionWithRole", [
                okT,
                0,
                "0x",
                0,
                role1,
                false,
              ])
            )
          )
      } else if (a < 58) {
        // direct execution by a module
        const m = pick([...MODULES, "x"] as const)
        const module = m === "x" ? addr.x : modAddr(m)
        const entry = pick([
          "withRole",
          "withRole",
          "fromModule",
          "returnData",
        ] as const)
        const c = randomCall()
        const shouldRevert = entry === "withRole" ? chance(0.5) : false
        const role =
          entry === "withRole"
            ? pick(EXEC_ROLES)
            : (model.defaults.get(module.toLowerCase()) ?? ZeroHash)
        const data =
          entry === "withRole"
            ? R.interface.encodeFunctionData("execTransactionWithRole", [
                c.to,
                c.value,
                c.data,
                c.operation,
                role,
                shouldRevert,
              ])
            : R.interface.encodeFunctionData(
                entry === "fromModule"
                  ? "execTransactionFromModule"
                  : "execTransactionFromModuleReturnData",
                [c.to, c.value, c.data, c.operation]
              )
        const predicted = model.enabled.has(module.toLowerCase())
          ? predictExec(module, role, c, shouldRevert)
          : { error: "NotAuthorized" }
        const r = await at(() =>
          outcome(w, () =>
            m === "x"
              ? x.sendTransaction({ to: addr.R, data, ...G })
              : asModule(m as Mod, data)
          )
        )
        await check(
          `step ${step} direct ${m} ${entry} ${c.kind}`,
          predicted,
          r,
          module,
          role,
          c,
          sentBefore
        )
      } else if (a < 95) {
        // relayed execution
        const c = randomCall()
        const shouldRevert = chance(0.5)
        const role = pick(EXEC_ROLES)
        const m: RoleTx = {
          to: c.to,
          value: c.value,
          data: c.data,
          operation: c.operation,
          roleKey: role,
          shouldRevert,
          salt: randomKey(),
        }
        const kind = pick([
          "e1",
          "e1",
          "e1",
          "e2",
          "e2",
          "S",
          "S",
          "S",
          "x",
          "short",
          "sentinel",
          "eoa1271",
          "crossDomain",
          "tamper",
          "replay",
          "replay",
        ] as const)
        let sig: string
        let signer: string | undefined // who is authenticated, if anyone
        let sub = m
        if (kind === "e1" || kind === "e2" || kind === "x") {
          const s = kind === "e1" ? e1 : kind === "e2" ? e2 : x
          sig = await w.sign(s, addr.R, m)
          signer = await s.getAddress()
        } else if (kind === "S") {
          const d = w.digest(addr.R, m)
          if (model.mode === 0 && chance(0.6)) {
            await at(() => S.approve(d))
            model.approved.add(d)
          }
          sig = concat([addr.S, hexlify(randomBytes(int(30)))])
          signer = validS(d) ? addr.S : undefined
        } else if (kind === "short") {
          sig = hexlify(randomBytes(int(20)))
        } else if (kind === "sentinel") {
          sig = concat([SENTINEL, "0x00"])
        } else if (kind === "eoa1271") {
          sig = concat([addr.e1, hexlify(randomBytes(5))])
        } else if (kind === "crossDomain") {
          sig = await w.sign(e1, addr.R2, m)
        } else if (kind === "tamper") {
          sig = await w.sign(e1, addr.R, m)
          sub = { ...m, salt: randomKey() }
        } else {
          if (!used.length) continue
          const u = pick(used)
          sub = u.m
          sig = u.sig
          // a contract signer answers by its current mode
          signer =
            u.signer === addr.S
              ? validS(w.digest(addr.R, u.m))
                ? addr.S
                : undefined
              : u.signer
        }
        const c2: Call =
          sub === m
            ? c
            : {
                ...c,
                to: sub.to,
                value: sub.value,
                data: sub.data,
                operation: sub.operation,
              }
        // kinds whose signature belongs to the message: replay keeps its call
        const call: Call =
          kind === "replay" ? (used.find((u) => u.m === sub) as any).call : c2
        const d = w.digest(addr.R, sub)
        let predicted: any
        if (!signer || !model.enabled.has(signer.toLowerCase()))
          predicted = { error: "NotAuthorized" }
        else if (model.consumed.has(`${signer.toLowerCase()}:${d}`))
          predicted = { error: "HashAlreadyConsumed" }
        else
          predicted = predictExec(signer, sub.roleKey, call, sub.shouldRevert)
        const r = await at(() =>
          outcome(w, () =>
            R.connect(relayer).execTransactionWithSignature(
              sub.to,
              sub.value,
              sub.data,
              sub.operation,
              sub.roleKey,
              sub.shouldRevert,
              sub.salt,
              sig,
              G
            )
          )
        )
        await check(
          `step ${step} signed ${kind} ${call.kind}`,
          predicted,
          r,
          signer ?? "",
          sub.roleKey,
          call,
          sentBefore
        )
        if (signer && (r.result === "ok" || r.result === "false")) {
          model.consumed.add(`${signer.toLowerCase()}:${d}`)
          digests.push({ signer, digest: d })
          if (kind !== "replay") used.push({ m: sub, sig, signer, call } as any)
        }
      } else {
        // a signer cancels a digest it has not used yet
        const s = pick([e1, e2])
        const m: RoleTx = {
          to: okT,
          value: 1n,
          data: "0x",
          operation: 0,
          roleKey: role1,
          shouldRevert: true,
          salt: randomKey(),
        }
        const d = w.digest(addr.R, m)
        await at(() => R.connect(s).invalidate(d))
        const signer = await s.getAddress()
        model.consumed.add(`${signer.toLowerCase()}:${d}`)
        digests.push({ signer, digest: d })
        used.push({
          m,
          sig: await w.sign(s, addr.R, m),
          signer,
          call: { kind: "send", to: okT, value: 1n, data: "0x", operation: 0 },
        } as any)
        bump(tally, "invalidate")
      }

      if (step % 50 === 49)
        for (const { signer, digest } of digests)
          expect(await R.consumed(signer, digest), "consumed").to.equal(true)
    }

    // memberships the model holds are the ones Roles reports
    for (const role of [role1, role2])
      for (const m of MODULES) {
        const mem = model.members.get(memKey(role, modAddr(m)))
        const active = !!mem && model.now >= mem.start && model.now <= mem.end
        expect(await R.isMember(role, modAddr(m)), `isMember ${m}`).to.equal(
          active
        )
      }

    const outcomes = new Map<string, number>()
    for (const [k, n] of Object.entries(tally)) {
      const m = k.match(/(direct|signed) .* (\S+)$/)
      if (m)
        outcomes.set(
          `${m[1]} ${m[2]}`,
          (outcomes.get(`${m[1]} ${m[2]}`) ?? 0) + n
        )
      else outcomes.set(k, (outcomes.get(k) ?? 0) + n)
    }
    console.log(
      "      " +
        [...outcomes]
          .sort()
          .map(([k, n]) => `${k}: ${n}`)
          .join("\n      ")
    )
  })
})
