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
 *   another Roles Modifier's digest, cancellation, a failed call reverting
 *   with ModuleTransactionFailed and rolling back digest consumption;
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
 * membership updates and uses, ether sent. It also requires that the default
 * run reaches every kind of outcome. `ATTRIBUTION_STEPS` (default 800) and
 * `ATTRIBUTION_SEED` (default 1); fewer steps or another seed skip that
 * requirement, as which outcomes a run reaches depends on both.
 */
import assert from "node:assert/strict"
import { randomBytes } from "node:crypto"
import { after, describe, it } from "node:test"
import { network } from "hardhat"
import {
  concat,
  decodeErrorResult,
  encodeErrorResult,
  encodeFunctionData,
  hashTypedData,
  isAddressEqual,
  parseAbi,
  parseEther,
  parseEventLogs,
  parseSignature,
  recoverAddress,
  toFunctionSelector,
  toHex,
  zeroHash,
} from "viem"
import type { Address, Hex, TransactionReceipt, WalletClient } from "viem"
import type { Abi, AbiError, AbiFunction, AbiParameter } from "abitype"
import { generatePrivateKey, privateKeyToAccount } from "viem/accounts"

import { extractRevertData } from "../../../evm/test/utils.js"
import type { RolesContract } from "../../../evm/test/utils.js"
import { safeAbi as abiSafe } from "../eip712/setup/safe-deployments/index.js"
import { deploySafe } from "../eip712/setup/safe.js"
import deployMastercopies from "../eip712/setup/deploy-mastercopies/index.js"
import {
  Encoding,
  ExecutionOptions as Options,
  NO_DEADLINE,
  Operator,
  count,
  deployRoles,
  encodeMultiSend,
  execSafe,
  prng,
  randomKey,
  ROLE_TX_TYPES,
} from "./helpers.js"
import type { RoleTx as SharedRoleTx } from "./helpers.js"

const connection = await network.create()
const { viem, networkHelpers } = connection
const { time } = networkHelpers

/** The run that reaches every outcome below `required`. */
const FULL_STEPS = 800
const FULL_SEED = 1
const STEPS = Number(process.env.ATTRIBUTION_STEPS ?? FULL_STEPS)
const SEED = Number(process.env.ATTRIBUTION_SEED ?? FULL_SEED)
const { int, pick, chance } = prng(SEED)

const SENTINEL = "0x0000000000000000000000000000000000000001" as Address
/** Enough gas for every call: with an estimated limit, a call through
 *  non-reverting IAvatar entrypoints (`execTransactionFromModule*`) that fails
 *  without reverting can be given too little gas. */
const G = { gas: 15_000_000n }

/** As signed here: amounts are bigints. */
type RoleTx = SharedRoleTx & { value: bigint; deadline: bigint }

const safeLogAbi = parseAbi([
  "event ExecutionFromModuleSuccess(address indexed module)",
  "event ExecutionFromModuleFailure(address indexed module)",
])

/* ------------------------------------------------------------------ setup */

/** Everything the cases share. */
async function world() {
  await deployMastercopies(viem)
  const [ownerA, e1, e2, x, relayer] = await viem.getWalletClients()
  const publicClient = await viem.getPublicClient()
  const safe = await deploySafe(
    {
      owners: [ownerA.account.address],
      threshold: 1,
      creationNonce: BigInt(randomKey()),
    },
    ownerA
  )
  const R = await deployRoles(viem, ownerA.account.address, safe)
  const R2 = await deployRoles(viem, ownerA.account.address, safe)
  for (const r of [R, R2])
    await execSafe(
      ownerA,
      safe,
      safe,
      encodeFunctionData({
        abi: abiSafe,
        functionName: "enableModule",
        args: [r.address],
      })
    )
  await ownerA.sendTransaction({ to: safe, value: parseEther("10") })

  const H = await viem.deployContract("Hostile")
  const S = await viem.deployContract("Signer1271")
  const Rev = await viem.deployContract("Reverter")
  const multiSend = await viem.deployContract("MultiSend")
  const unwrapper = await viem.deployContract("MultiSendUnwrapper")
  const okT = privateKeyToAccount(generatePrivateKey()).address
  const K1 = randomKey()
  const role1 = randomKey()
  const role2 = randomKey()

  const addr = {
    H: H.address,
    S: S.address,
    Rev: Rev.address,
    multiSend: multiSend.address,
    R: R.address,
    R2: R2.address,
    e1: e1.account.address,
    e2: e2.account.address,
    x: x.account.address,
  }

  for (const r of [R, R2]) {
    await r.write.setTransactionUnwrapper(
      [
        addr.multiSend,
        toFunctionSelector("multiSend(bytes)"),
        unwrapper.address,
      ],
      { account: ownerA.account }
    )
    await r.write.setAllowance([K1, 1000n, 0n, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    // role 1: ether to okT within K1, the hostile target, the reverter,
    // batches (MultiSend is unwrapped, its entries are checked)
    for (const t of [okT, addr.H, addr.Rev])
      await r.write.scopeTarget([role1, t], { account: ownerA.account })
    await r.write.allowTarget(
      [
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
        Options.Send,
      ],
      { account: ownerA.account }
    )
    await r.write.allowTarget([role1, addr.H, [], Options.None], {
      account: ownerA.account,
    })
    await r.write.allowTarget([role1, addr.Rev, [], Options.None], {
      account: ownerA.account,
    })
    // role 2: okT without ether
    await r.write.scopeTarget([role2, okT], { account: ownerA.account })
    await r.write.allowTarget([role2, okT, [], Options.None], {
      account: ownerA.account,
    })
  }

  const chainId = await publicClient.getChainId()
  const digest = (r: Address, m: RoleTx) =>
    hashTypedData({
      domain: { chainId, verifyingContract: r },
      types: ROLE_TX_TYPES,
      primaryType: "RoleTx",
      message: m,
    })
  const sign = (s: WalletClient, r: Address, m: RoleTx) =>
    s.signTypedData({
      account: s.account!,
      domain: { chainId, verifyingContract: r },
      types: ROLE_TX_TYPES,
      primaryType: "RoleTx",
      message: m,
    })

  const errorBySelector = new Map<Hex, string>(
    (R.abi as Abi)
      .filter((item): item is AbiError => item.type === "error")
      .map((item) => [
        toFunctionSelector({
          ...item,
          type: "function",
        } as unknown as AbiFunction),
        item.name,
      ])
  )

  return {
    ownerA,
    e1,
    e2,
    x,
    relayer,
    publicClient,
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
    errorBySelector,
  }
}

type World = Awaited<ReturnType<typeof world>>

/** What the Reverter target reverts with. */
const REVERTER_DATA = encodeErrorResult({
  abi: parseAbi(["error Error(string)"]),
  errorName: "Error",
  args: ["reverter"],
})

const errorName = (w: World, e: unknown): string => {
  const data = extractRevertData(e)
  if (data && data.length >= 10) {
    try {
      const parsed = decodeErrorResult({ abi: w.R.abi, data })
      return parsed.errorName
    } catch {
      return data.slice(0, 10)
    }
  }
  const msg =
    e instanceof Error
      ? ((e as { shortMessage?: string }).shortMessage ?? e.message)
      : String(e)
  return `unparsed: ${msg}`
}

/** The outcome of a transaction: "ok" / "false" (the avatar's call failed on
 *  an IAvatar entrypoint) or the custom error. */
async function outcome(
  w: World,
  send: () => Promise<Hex>
): Promise<{ result: string; receipt?: TransactionReceipt; data?: Hex }> {
  try {
    const hash = await send()
    const receipt = await w.publicClient.waitForTransactionReceipt({ hash })
    const safeLogs = parseEventLogs({
      abi: safeLogAbi,
      logs: receipt.logs.filter((l) => isAddressEqual(l.address, w.safe)),
    })
    const result = safeLogs.some(
      (l) => l.eventName === "ExecutionFromModuleFailure"
    )
      ? "false"
      : "ok"
    return { result, receipt }
  } catch (e) {
    return { result: errorName(w, e), data: extractRevertData(e) }
  }
}

const sel = (name: string) => toFunctionSelector(`${name}()`)

/** The calls the hostile target makes into Roles while it is being called:
 *  all four execution entry points, as a module with a valid membership. */
async function reentryPlan(w: World): Promise<Hex[]> {
  const m: RoleTx = {
    to: w.okT,
    value: 0n,
    data: "0x",
    operation: 0,
    roleKey: w.role1,
    salt: randomKey(),
    deadline: NO_DEADLINE,
  }
  const sig = concat([w.addr.S, toHex(randomBytes(10))])
  return [
    encodeFunctionData({
      abi: w.R.abi,
      functionName: "execTransactionWithRole",
      args: [w.okT, 0n, "0x", 0, w.role1],
    }),
    encodeFunctionData({
      abi: w.R.abi,
      functionName: "execTransactionFromModule",
      args: [w.okT, 0n, "0x", 0],
    }),
    encodeFunctionData({
      abi: w.R.abi,
      functionName: "execTransactionFromModuleReturnData",
      args: [w.okT, 0n, "0x", 0],
    }),
    encodeFunctionData({
      abi: w.R.abi,
      functionName: "execTransactionWithRoleSigned",
      args: [m, sig],
    }),
  ]
}

/** A default argument of each type, for calling any function. */
function defaultArg(t: AbiParameter, w: World): unknown {
  const arrMatch = t.type.match(/^(.*)\[(\d*)\]$/)
  if (arrMatch) {
    const len = arrMatch[2] ? Number(arrMatch[2]) : 0
    const child = { ...t, type: arrMatch[1] } as AbiParameter
    return len > 0
      ? Array.from({ length: len }, () => defaultArg(child, w))
      : []
  }
  if (t.type === "tuple" && "components" in t && t.components) {
    return t.components.map((c) => defaultArg(c, w))
  }
  if (t.type === "address") return w.addr.H
  if (t.type === "bool") return false
  if (t.type === "bytes") return "0x"
  if (t.type === "string") return ""
  if (t.type.startsWith("bytes"))
    return w.role1.slice(0, 2 + 2 * Number(t.type.slice(5)))
  return 0n
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
    await R.write.grantRole([addr.H, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    await R.write.grantRole([addr.S, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    await R.write.setDefaultRole([addr.H, role1], { account: ownerA.account })
    await S.write.setMode([1])
    const plan = await reentryPlan(w)

    // at the top level, each of these executes
    for (const data of plan) {
      const r = await outcome(w, () => H.write.act([addr.R, data]))
      assert.equal(r.result, "ok")
    }
    // from inside an execution (the avatar calls H), each reverts; a fresh
    // plan, whose signed entry has not been consumed
    const inner = await reentryPlan(w)
    await H.write.setPlan([inner.map(() => addr.R), inner, false])
    const r = await outcome(w, () =>
      H.write.act([
        addr.R,
        encodeFunctionData({
          abi: R.abi,
          functionName: "execTransactionWithRole",
          args: [addr.H, 0n, "0x12345678", 0, role1],
        }),
      ])
    )
    assert.equal(r.result, "ok")
    const results = await Promise.all(
      inner.map((_, i) => H.read.results([BigInt(i)]))
    )
    assert.deepEqual(
      results,
      inner.map(() => sel("Reentrancy"))
    )
  })

  it("from inside an executed call, only Roles functions keyed by the caller succeed", async () => {
    const w = await world()
    const { R, H, ownerA, role1, addr } = w
    await R.write.grantRole([addr.H, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    const fns = (R.abi as Abi).filter(
      (f): f is AbiFunction =>
        f.type === "function" && !["view", "pure"].includes(f.stateMutability)
    )
    const datas = fns.map((f) =>
      encodeFunctionData({
        abi: [f],
        functionName: f.name,
        args: f.inputs.map((i) => defaultArg(i, w)),
      })
    )
    await H.write.setPlan([datas.map(() => addr.R), datas, false])
    await R.write.grantRole([addr.e1, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    const r2 = await outcome(w, () =>
      R.write.execTransactionWithRole([addr.H, 0n, "0x12345678", 0, role1], {
        account: w.e1.account,
      })
    )
    assert.equal(r2.result, "ok")

    const table: Record<string, string> = {}
    for (const [i, f] of fns.entries()) {
      const s = await H.read.results([BigInt(i)])
      table[f.name] =
        s === "0x00000000" ? "ok" : (w.errorBySelector.get(s) ?? s)
    }
    const succeeded = Object.keys(table).filter((k) => table[k] === "ok")
    assert.deepEqual(succeeded.sort(), ["invalidate", "renounceRole"])
    for (const f of [
      "execTransactionFromModule",
      "execTransactionFromModuleReturnData",
      "execTransactionWithRole",
      "execTransactionWithRoleSigned",
    ])
      assert.equal(table[f], "Reentrancy")
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
    const { R, S, ownerA, publicClient, role1, addr, relayer, okT } = w
    await R.write.grantRole([addr.S, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    // inside the check, S tries a direct execution (as a member module)
    await S.write.setReenter([
      addr.R,
      encodeFunctionData({
        abi: R.abi,
        functionName: "execTransactionWithRole",
        args: [okT, 0n, "0x", 0, role1],
      }),
    ])
    await S.write.setMode([4])
    const m: RoleTx = {
      to: okT,
      value: 7n,
      data: "0x",
      operation: 0,
      roleKey: role1,
      salt: randomKey(),
      deadline: NO_DEADLINE,
    }
    const sig = concat([addr.S, "0xabcdef"])
    const before = await publicClient.getBalance({ address: okT })
    const r = await outcome(w, () =>
      R.write.execTransactionWithRoleSigned([m, sig], {
        account: relayer.account,
      })
    )
    // mode 4 answers valid only if the reentry failed
    assert.equal(r.result, "ok")
    assert.equal(await publicClient.getBalance({ address: okT }), before + 7n)
    assert.equal(await R.read.consumed([addr.S, w.digest(addr.R, m)]), true)
  })

  it("the signature parser and replay protection", async () => {
    const w = await world()
    const { R, R2, S, ownerA, e1, x, role1, addr, relayer, okT } = w
    await R.write.grantRole([addr.e1, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    await R.write.grantRole([addr.S, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    await R2.write.grantRole([addr.e1, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    const tx = (over: Partial<RoleTx> = {}): RoleTx => ({
      to: okT,
      value: 1n,
      data: "0x",
      operation: 0,
      roleKey: role1,
      salt: randomKey(),
      deadline: NO_DEADLINE,
      ...over,
    })
    const relay = (r: RolesContract, m: RoleTx, sig: Hex) =>
      outcome(w, () =>
        r.write.execTransactionWithRoleSigned([m, sig], {
          account: relayer.account,
        })
      )

    // too short: no signer
    assert.equal(
      (await relay(R, tx(), ("0x" + "11".repeat(19)) as Hex)).result,
      "NotAuthorized"
    )
    // the module list's sentinel (address 1, a precompile without code)
    await S.write.setMode([1])
    assert.equal(
      (await relay(R, tx(), concat([SENTINEL, "0x00"]))).result,
      "NotAuthorized"
    )
    // an EOA module named as a contract signer: no code, not valid
    assert.equal(
      (await relay(R, tx(), concat([addr.e1, "0x00"]))).result,
      "NotAuthorized"
    )
    // a non-module's valid ECDSA signature
    const mx = tx()
    assert.equal(
      (await relay(R, mx, await w.sign(x, addr.R, mx))).result,
      "NotAuthorized"
    )
    // a module's signature for another Roles Modifier
    const m2 = tx()
    assert.equal(
      (await relay(R, m2, await w.sign(e1, addr.R2, m2))).result,
      "NotAuthorized"
    )
    // a tampered field
    const mt = tx()
    assert.equal(
      (await relay(R, { ...mt, value: 2n }, await w.sign(e1, addr.R, mt)))
        .result,
      "NotAuthorized"
    )
    // valid once, then consumed
    const m = tx()
    const sig = await w.sign(e1, addr.R, m)
    assert.equal((await relay(R, m, sig)).result, "ok")
    assert.equal((await relay(R, m, sig)).result, "HashAlreadyConsumed")
    // malleated (s -> n - s, v flipped): ecrecover still gives e1, and the
    // digest is consumed whatever the signature's bytes
    const n =
      0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n
    const { r: sr, s: ss, v: sv } = parseSignature(sig)
    const malleated = concat([
      sr,
      toHex(n - BigInt(ss), { size: 32 }),
      sv === 27n ? "0x1c" : "0x1b",
    ])
    assert.equal((await relay(R, m, malleated)).result, "HashAlreadyConsumed")
    // cancelled before use
    const mc = tx()
    await R.write.invalidate([w.digest(addr.R, mc)], { account: e1.account })
    assert.equal(
      (await relay(R, mc, await w.sign(e1, addr.R, mc))).result,
      "HashAlreadyConsumed"
    )

    // a 65-byte contract signature (20 + 45 bytes) is tried as ECDSA first:
    // if that recovers an address, it is the signer (here not a module), and
    // the contract's valid signature is rejected; if recovery fails (here
    // `v` = 0) it is checked by ERC-1271
    const m65 = tx()
    const d65 = w.digest(addr.R, m65)
    let recovering: Hex | undefined
    while (!recovering) {
      // r starts with the signer's address; a small s; v = 27
      const sig65 = concat([
        addr.S,
        toHex(randomBytes(12)),
        "0x00",
        toHex(randomBytes(31)),
        "0x1b",
      ])
      try {
        await recoverAddress({ hash: d65, signature: sig65 })
        recovering = sig65
      } catch {}
    }
    assert.equal((await relay(R, m65, recovering)).result, "NotAuthorized")
    assert.equal(
      (
        await relay(
          R,
          m65,
          concat([recovering.slice(0, 2 + 64 * 2) as Hex, "0x00"])
        )
      ).result,
      "ok"
    )

    // a failed relayed call reverts with ModuleTransactionFailed and rolls back digest consumption
    const fail = tx({ to: addr.Rev, value: 0n })
    assert.equal(
      (await relay(R, fail, await w.sign(e1, addr.R, fail))).result,
      "ModuleTransactionFailed"
    )
    assert.equal(
      await R.read.consumed([addr.e1, w.digest(addr.R, fail)]),
      false
    )
  })

  it("under-supplying gas on a relayed call reverts instead of burning the signature", async () => {
    const w = await world()
    const { R, H, ownerA, e1, role1, addr, relayer } = w
    await R.write.grantRole([addr.e1, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    // the call to H costs some gas: H tries the four entry points
    const plan = await reentryPlan(w)
    await H.write.setPlan([plan.map(() => addr.R), plan, false])
    const relayWithGas = async (gasLimit: number) => {
      const m: RoleTx = {
        to: addr.H,
        value: 0n,
        data: "0x12345678",
        operation: 0,
        roleKey: role1,
        salt: randomKey(),
        deadline: NO_DEADLINE,
      }
      const sig = await w.sign(e1, addr.R, m)
      const runs = await H.read.runs()
      const r = await outcome(w, () =>
        R.write.execTransactionWithRoleSigned([m, sig], {
          account: relayer.account,
          gas: BigInt(gasLimit),
        })
      )
      return {
        result: r.result,
        ran: (await H.read.runs()) > runs,
        consumed: await R.read.consumed([addr.e1, w.digest(addr.R, m)]),
      }
    }
    /** Try gas limits in steps of 2000 until the transaction succeeds:
     *  every failing limit must revert with neither the call running nor
     *  the digest consumed. */
    let succeeded:
      | { result: string; ran: boolean; consumed: boolean; gas: number }
      | undefined
    for (let g = 40_000; g < 3_000_000; g += 2_000) {
      const r = await relayWithGas(g)
      if (r.result === "ok") {
        succeeded = { ...r, gas: g }
        break
      }
      assert.notEqual(r.result, "false", `gas ${g}`)
      assert.equal(r.ran, false, `gas ${g}`)
      assert.equal(r.consumed, false, `gas ${g}`)
    }
    assert.ok(succeeded)
    assert.equal(succeeded.result, "ok")
    assert.equal(succeeded.ran, true)
    assert.equal(succeeded.consumed, true)
    console.log(
      `      lowest gas limit: ${succeeded.gas} (call runs; every lower limit reverted without burning digest)`
    )
  })

  it("memberships: a batch is one use, renouncing during the own execution, disabled modules", async () => {
    const w = await world()
    const { R, H, ownerA, e1, role1, addr, okT } = w
    const usesOf = (rc?: TransactionReceipt) =>
      parseEventLogs({
        abi: R.abi,
        eventName: ["UpdateRole", "RevokeRole"],
        logs: (rc?.logs ?? []).filter((l) =>
          isAddressEqual(l.address, R.address)
        ),
      }).map((p) =>
        p.eventName === "RevokeRole" ? "revoked" : p.args.usesLeft.toString()
      )

    // a batch of three entries uses one of three uses
    await R.write.grantRole([addr.e1, role1, 0n, 0n, 3n], {
      account: ownerA.account,
    })
    const batch = encodeMultiSend([
      { to: okT, value: 1n },
      { to: okT, value: 2n },
      { to: okT, value: 3n },
    ])
    const b = await outcome(w, () =>
      R.write.execTransactionWithRole([addr.multiSend, 0n, batch, 1, role1], {
        account: e1.account,
      })
    )
    assert.equal(b.result, "ok")
    assert.deepEqual(usesOf(b.receipt), ["2"])

    // H renounces role 1 while executing with it: settlement reads the
    // membership after execution, so the renouncement stays
    await R.write.grantRole([addr.H, role1, 0n, 0n, 5n], {
      account: ownerA.account,
    })
    const renounce = encodeFunctionData({
      abi: R.abi,
      functionName: "renounceRole",
      args: [role1],
    })
    await H.write.setPlan([[addr.R], [renounce], false])
    const call = encodeFunctionData({
      abi: R.abi,
      functionName: "execTransactionWithRole",
      args: [addr.H, 0n, "0x12345678", 0, role1],
    })
    const r1 = await outcome(w, () => H.write.act([addr.R, call]))
    assert.equal(r1.result, "ok")
    assert.equal(await H.read.results([0n]), "0x00000000")
    assert.deepEqual(usesOf(r1.receipt), ["revoked"])
    assert.equal((await R.read.membershipOf([addr.H, role1]))[0], false)
    // the same with unlimited uses
    await R.write.grantRole([addr.H, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    const r2 = await outcome(w, () => H.write.act([addr.R, call]))
    assert.equal(r2.result, "ok")
    assert.deepEqual(usesOf(r2.receipt), ["revoked"])
    assert.equal((await R.read.membershipOf([addr.H, role1]))[0], false)

    // a module disabled after the grant cannot execute, directly or signed
    await R.write.grantRole([addr.e1, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    const [mods] = await R.read.getModulesPaginated([SENTINEL, 100n])
    const i = mods.findIndex((m) => isAddressEqual(m, addr.e1))
    await R.write.disableModule([i === 0 ? SENTINEL : mods[i - 1], addr.e1], {
      account: ownerA.account,
    })
    assert.equal((await R.read.membershipOf([addr.e1, role1]))[0], false)
    assert.notEqual((await R.read.membershipOf([addr.e1, role1]))[3], 0n)
    assert.equal(
      (
        await outcome(w, () =>
          R.write.execTransactionWithRole([okT, 0n, "0x", 0, role1], {
            account: e1.account,
          })
        )
      ).result,
      "NotAuthorized"
    )
    const m: RoleTx = {
      to: okT,
      value: 0n,
      data: "0x",
      operation: 0,
      roleKey: role1,
      salt: randomKey(),
      deadline: NO_DEADLINE,
    }
    const sig = await w.sign(e1, addr.R, m)
    assert.equal(
      (
        await outcome(w, () =>
          R.write.execTransactionWithRoleSigned([m, sig], {
            account: w.relayer.account,
          })
        )
      ).result,
      "NotAuthorized"
    )
  })

  it("an execution can nest an execution through another Roles Modifier on the same Safe", async () => {
    const w = await world()
    const { R, R2, H, ownerA, e1, role1, addr, okT, K1 } = w
    await R.write.grantRole([addr.e1, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    await R2.write.grantRole([addr.H, role1, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    // inside e1's execution through R, H executes through R2
    const inner = encodeFunctionData({
      abi: R2.abi,
      functionName: "execTransactionWithRole",
      args: [okT, 5n, "0x", 0, role1],
    })
    await H.write.setPlan([[addr.R2], [inner], false])
    const r = await outcome(w, () =>
      R.write.execTransactionWithRole([addr.H, 0n, "0x12345678", 0, role1], {
        account: e1.account,
      })
    )
    assert.equal(r.result, "ok")
    assert.equal(await H.read.results([0n]), "0x00000000")
    // each Roles guards only itself, and settles its own allowance
    assert.equal((await R2.read.allowances([K1]))[3], 995n)
    assert.equal((await R.read.allowances([K1]))[3], 1000n)
  })

  /* ------------------------------------------------------------ the fuzz */

  it(`a reference model predicts every outcome (${STEPS} random steps)`, async () => {
    const w = await world()
    const {
      R,
      H,
      S,
      ownerA,
      e1,
      e2,
      x,
      relayer,
      publicClient,
      role1,
      role2,
      addr,
      okT,
      K1,
    } = w

    type Mem = { start: bigint; end: bigint; uses: bigint | "inf" }
    const MODULES = ["e1", "e2", "H", "S"] as const
    type Mod = (typeof MODULES)[number]
    const modAddr = (m: Mod) => addr[m]
    const ROLES = [role1, role2, zeroHash]
    const EXEC_ROLES = [role1, role1, role1, role2, role2, zeroHash]

    const plan = await reentryPlan(w)
    await H.write.setPlan([plan.map(() => addr.R), plan, false])

    const model = {
      now: (await publicClient.getBlock()).timestamp,
      enabled: new Set<string>(),
      members: new Map<string, Mem>(),
      defaults: new Map<string, Hex>(),
      allowance: 1000n,
      consumed: new Set<string>(),
      approved: new Set<string>(),
      mode: 0,
    }
    const memKey = (role: string, m: string) => `${role}:${m.toLowerCase()}`
    const digests: { signer: Address; digest: Hex }[] = []
    const used: { m: RoleTx; sig: Hex; signer: Address; call: Call }[] = []
    // every digest a known signer submitted, to check its consumption at the end
    const tried = new Map<string, { signer: Address; digest: Hex }>()
    const tally: Record<string, number> = {}
    /** Whether S accepts a digest now. */
    const validS = (d: string) =>
      model.mode === 1 ||
      model.mode === 4 ||
      (model.mode === 0 && model.approved.has(d))

    // a timestamp for every transaction, so predictions are exact
    const at = async <T>(f: () => Promise<T>): Promise<T> => {
      model.now += 1n
      await time.setNextBlockTimestamp(model.now)
      return f()
    }
    const asModule = (m: Mod, data: Hex) =>
      m === "e1"
        ? e1.sendTransaction({ to: addr.R, data, ...G })
        : m === "e2"
          ? e2.sendTransaction({ to: addr.R, data, ...G })
          : m === "H"
            ? H.write.act([addr.R, data], G)
            : S.write.act([addr.R, data], G)

    type Call = {
      kind: string
      to: Address
      value: bigint
      data: Hex
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
        to: x.account.address,
        value: 0n,
        data: "0x",
        operation: 0,
      }
    }

    /** What `_authenticate` + `_authorize` + the call do, from the model. */
    const predictExec = (
      module: string,
      role: Hex,
      c: Call,
      revertsOnFail: boolean
    ) => {
      if (role === zeroHash) return { error: "NoMembership" }
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
      if (!success && revertsOnFail) return { error: "ModuleTransactionFailed" }
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
      r: { result: string; receipt?: TransactionReceipt; data?: Hex },
      module: string,
      role: Hex,
      c: Call,
      sentBefore: bigint
    ) => {
      const want = predicted.error ?? (predicted.success ? "ok" : "false")
      assert.equal(r.result, want, `${label}: outcome`)
      if (want === "ModuleTransactionFailed") {
        // the only executed call the generator makes fail is the reverter's
        assert.equal(c.kind, "revert", `${label}: the call that failed`)
        const decoded = decodeErrorResult({ abi: R.abi, data: r.data! })
        assert.equal(decoded.errorName, "ModuleTransactionFailed")
        assert.equal(
          decoded.args?.[0],
          REVERTER_DATA,
          `${label}: inner revert data`
        )
      }
      count(tally, `${label} ${want}`)
      const ok = want === "ok"
      if (ok) {
        model.allowance -= predicted.charge!
        const mem = predicted.mem!
        const events = parseEventLogs({
          abi: R.abi,
          eventName: ["UpdateRole", "RevokeRole"],
          logs: (r.receipt!.logs ?? []).filter((l) =>
            isAddressEqual(l.address, addr.R)
          ),
        }).map((p) =>
          p.eventName === "RevokeRole" ? "revoked" : p.args.usesLeft.toString()
        )
        if (mem.uses === "inf")
          assert.deepEqual(events, [], `${label}: membership`)
        else if (mem.uses <= 1n) {
          assert.deepEqual(events, ["revoked"], `${label}: membership`)
          model.members.delete(memKey(role, module))
        } else {
          assert.deepEqual(
            events,
            [(mem.uses - 1n).toString()],
            `${label}: membership`
          )
          mem.uses -= 1n
        }
        if (c.kind === "reenter") {
          const n = Number(await H.read.resultCount())
          for (let i = 0; i < n; i++)
            assert.equal(
              await H.read.results([BigInt(i)]),
              sel("Reentrancy"),
              `${label}: reentry`
            )
          count(tally, "reentries refused")
        }
      }
      const sent =
        ok && (c.kind === "send" || c.kind === "batch")
          ? c.kind === "send"
            ? c.value
            : c.entries!.reduce((a, b) => a + b, 0n)
          : 0n
      assert.equal(
        await publicClient.getBalance({ address: okT }),
        sentBefore + sent,
        `${label}: ether sent`
      )
      assert.equal(
        (await R.read.allowances([K1]))[3],
        model.allowance,
        `${label}: allowance`
      )
    }

    // start with every module an unlimited member of both roles
    for (const m of MODULES)
      for (const role of [role1, role2]) {
        await at(() =>
          R.write.grantRole([modAddr(m), role, 0n, 0n, 0n], {
            account: ownerA.account,
          })
        )
        model.members.set(memKey(role, modAddr(m)), {
          start: 0n,
          end: 2n ** 64n - 1n,
          uses: "inf",
        })
        model.enabled.add(modAddr(m).toLowerCase())
      }
    for (const m of MODULES) {
      await at(() =>
        R.write.setDefaultRole([modAddr(m), role1], {
          account: ownerA.account,
        })
      )
      model.defaults.set(modAddr(m).toLowerCase(), role1)
    }

    for (let step = 0; step < STEPS; step++) {
      const a = int(100)
      const sentBefore = await publicClient.getBalance({ address: okT })

      if (a < 12) {
        // owner grants a membership (and enables the module)
        const m = pick(MODULES)
        const role = pick([role1, role2])
        const start = chance(0.8) ? 0n : model.now + BigInt(int(2000)) - 500n
        const end = chance(0.6) ? 0n : model.now + BigInt(int(4000))
        const uses = chance(0.5) ? 0n : BigInt(1 + int(4))
        await at(() =>
          R.write.grantRole(
            [modAddr(m), role, start < 0n ? 0n : start, end, uses],
            { account: ownerA.account }
          )
        )
        model.members.set(memKey(role, modAddr(m)), {
          start: start < 0n ? 0n : start,
          end: end === 0n ? 2n ** 64n - 1n : end,
          uses: uses === 0n ? "inf" : uses,
        })
        model.enabled.add(modAddr(m).toLowerCase())
        count(tally, "grant")
      } else if (a < 14) {
        const m = pick(MODULES)
        const role = pick([role1, role2])
        await at(() =>
          R.write.revokeRole([modAddr(m), role], { account: ownerA.account })
        )
        model.members.delete(memKey(role, modAddr(m)))
        count(tally, "revoke")
      } else if (a < 15) {
        // a module renounces
        const m = pick(MODULES)
        const role = pick([role1, role2])
        await at(() =>
          asModule(
            m,
            encodeFunctionData({
              abi: R.abi,
              functionName: "renounceRole",
              args: [role],
            })
          )
        )
        model.members.delete(memKey(role, modAddr(m)))
        count(tally, "renounce")
      } else if (a < 18) {
        // owner disables or enables a module
        const m = pick(MODULES)
        const a_ = modAddr(m)
        if (model.enabled.has(a_.toLowerCase()) && chance(0.4)) {
          const [mods] = await R.read.getModulesPaginated([SENTINEL, 100n])
          const i = mods.findIndex((xAddr) => isAddressEqual(xAddr, a_))
          await at(() =>
            R.write.disableModule([i === 0 ? SENTINEL : mods[i - 1], a_], {
              account: ownerA.account,
            })
          )
          model.enabled.delete(a_.toLowerCase())
          count(tally, "disable")
        } else if (!model.enabled.has(a_.toLowerCase())) {
          await at(() =>
            R.write.enableModule([a_], { account: ownerA.account })
          )
          model.enabled.add(a_.toLowerCase())
          count(tally, "enable")
        }
      } else if (a < 20) {
        const m = pick(MODULES)
        const role = pick(ROLES)
        await at(() =>
          R.write.setDefaultRole([modAddr(m), role], {
            account: ownerA.account,
          })
        )
        model.defaults.set(modAddr(m).toLowerCase(), role)
        count(tally, "default role")
      } else if (a < 23) {
        model.now += BigInt(pick([10, 600, 3000]))
        count(tally, "time")
      } else if (a < 25) {
        const b = BigInt(int(1000))
        await at(() =>
          R.write.setAllowance([K1, b, 0n, 0n, 0n, 0n], {
            account: ownerA.account,
          })
        )
        model.allowance = b
        count(tally, "set allowance")
      } else if (a < 27) {
        model.mode = pick([0, 0, 1, 2, 3, 4, 5])
        await at(() => S.write.setMode([model.mode]))
        if (model.mode === 4)
          await at(() =>
            S.write.setReenter([
              addr.R,
              encodeFunctionData({
                abi: R.abi,
                functionName: "execTransactionWithRole",
                args: [okT, 0n, "0x", 0, role1],
              }),
            ])
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
        const revertsOnFail = entry === "withRole"
        const role =
          entry === "withRole"
            ? pick(EXEC_ROLES)
            : (model.defaults.get(module.toLowerCase()) ?? zeroHash)
        const data =
          entry === "withRole"
            ? encodeFunctionData({
                abi: R.abi,
                functionName: "execTransactionWithRole",
                args: [c.to, c.value, c.data, c.operation, role],
              })
            : encodeFunctionData({
                abi: R.abi,
                functionName:
                  entry === "fromModule"
                    ? "execTransactionFromModule"
                    : "execTransactionFromModuleReturnData",
                args: [c.to, c.value, c.data, c.operation],
              })
        const predicted = !model.enabled.has(module.toLowerCase())
          ? { error: "NotAuthorized" }
          : entry !== "withRole" && role === zeroHash
            ? { error: "NoDefaultRole" }
            : predictExec(module, role, c, revertsOnFail)
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
        const role = pick(EXEC_ROLES)
        // the transaction is mined at model.now + 1
        const deadline = pick([
          ...Array(6).fill(NO_DEADLINE),
          model.now + 1n,
          model.now + 1n + BigInt(int(1000)),
          model.now + 1n + BigInt(int(1000)),
          // expired
          model.now,
          0n,
        ])
        const m: RoleTx = {
          to: c.to,
          value: c.value,
          data: c.data,
          operation: c.operation,
          roleKey: role,
          salt: randomKey(),
          deadline,
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
        let sig: Hex
        let signer: Address | undefined // who is authenticated, if anyone
        let sub = m
        if (kind === "e1" || kind === "e2" || kind === "x") {
          const s = kind === "e1" ? e1 : kind === "e2" ? e2 : x
          sig = await w.sign(s, addr.R, m)
          signer = s.account.address
        } else if (kind === "S") {
          const d = w.digest(addr.R, m)
          if (model.mode === 0 && chance(0.6)) {
            await at(() => S.write.approve([d]))
            model.approved.add(d)
          }
          sig = concat([addr.S, toHex(randomBytes(int(30)))])
          signer = validS(d) ? addr.S : undefined
        } else if (kind === "short") {
          sig = toHex(randomBytes(int(20)))
        } else if (kind === "sentinel") {
          sig = concat([SENTINEL, "0x00"])
        } else if (kind === "eoa1271") {
          sig = concat([addr.e1, toHex(randomBytes(5))])
        } else if (kind === "crossDomain") {
          sig = await w.sign(e1, addr.R2, m)
        } else if (kind === "tamper") {
          sig = await w.sign(e1, addr.R, m)
          sub = chance(0.5)
            ? { ...m, salt: randomKey() }
            : { ...m, deadline: m.deadline === NO_DEADLINE ? 0n : NO_DEADLINE }
        } else {
          if (!used.length) continue
          const u = pick(used)
          sub = u.m
          sig = u.sig
          // a contract signer answers by its current mode
          signer = isAddressEqual(u.signer, addr.S)
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
          kind === "replay" ? used.find((u) => u.m === sub)!.call : c2
        const d = w.digest(addr.R, sub)
        let predicted: any
        if (!signer || !model.enabled.has(signer.toLowerCase()))
          predicted = { error: "NotAuthorized" }
        else if (model.consumed.has(`${signer.toLowerCase()}:${d}`))
          predicted = { error: "HashAlreadyConsumed" }
        // after the signature, before the membership
        else if (model.now + 1n > sub.deadline)
          predicted = { error: "SignatureExpired" }
        else predicted = predictExec(signer, sub.roleKey, call, true)
        if (signer)
          tried.set(`${signer.toLowerCase()}:${d}`, { signer, digest: d })
        const r = await at(() =>
          outcome(w, () =>
            R.write.execTransactionWithRoleSigned([sub, sig], {
              account: relayer.account,
              ...G,
            })
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
        if (signer && r.result === "ok") {
          model.consumed.add(`${signer.toLowerCase()}:${d}`)
          digests.push({ signer, digest: d })
          if (kind !== "replay") used.push({ m: sub, sig, signer, call })
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
          salt: randomKey(),
          deadline: NO_DEADLINE,
        }
        const d = w.digest(addr.R, m)
        await at(() => R.write.invalidate([d], { account: s.account }))
        const signer = s.account.address
        model.consumed.add(`${signer.toLowerCase()}:${d}`)
        digests.push({ signer, digest: d })
        used.push({
          m,
          sig: await w.sign(s, addr.R, m),
          signer,
          call: { kind: "send", to: okT, value: 1n, data: "0x", operation: 0 },
        })
        count(tally, "invalidate")
      }

      if (step % 50 === 49)
        for (const { signer, digest } of digests)
          assert.equal(
            await R.read.consumed([signer, digest]),
            true,
            "consumed"
          )
    }

    // memberships the model holds are the ones Roles reports
    for (const role of [role1, role2])
      for (const m of MODULES) {
        const mem = model.members.get(memKey(role, modAddr(m)))
        const active =
          !!mem &&
          model.now >= mem.start &&
          model.now <= mem.end &&
          model.enabled.has(modAddr(m).toLowerCase())
        assert.deepEqual(
          await R.read.membershipOf([modAddr(m), role]),
          mem
            ? [
                active,
                mem.start,
                mem.end,
                mem.uses === "inf" ? 2n ** 128n - 1n : mem.uses,
              ]
            : [false, 0n, 0n, 0n],
          `membership ${m}`
        )
      }
    // refused, failed and expired signatures stay unconsumed
    for (const [key, { signer, digest }] of tried)
      assert.equal(
        await R.read.consumed([signer, digest]),
        model.consumed.has(key),
        `consumed ${key}`
      )

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

    // Every step's outcome is checked against the model, but only the
    // outcomes a run reaches. Fail if the generator stops reaching one in
    // the default run; a shorter run (a smoke test) or another seed is not
    // expected to reach the rare ones.
    const reached = (re: RegExp) =>
      Object.entries(tally).reduce((n, [k, v]) => (re.test(k) ? n + v : n), 0)
    const required: [string, RegExp][] = [
      ["direct ok", / direct .* ok$/],
      ["direct false (IAvatar call fails)", / direct .* false$/],
      ["direct batch ok", / direct .* batch ok$/],
      ["direct by contract module ok", / direct [HS] .* ok$/],
      ["signed ok by EOA", / signed e[12] .* ok$/],
      ["signed ok by ERC-1271", / signed S .* ok$/],
      ["signed batch ok", / signed .* batch ok$/],
      ["signed replay refused", / signed replay .* HashAlreadyConsumed$/],
      ["ModuleTransactionFailed", / ModuleTransactionFailed$/],
      ["SignatureExpired", / signed .* SignatureExpired$/],
      ["signed tampered refused", / signed tamper .* NotAuthorized$/],
      ["ConditionViolation", / ConditionViolation$/],
      ["NoMembership", / NoMembership$/],
      ["MembershipExpired", / MembershipExpired$/],
      ["MembershipNotYetValid", / MembershipNotYetValid$/],
      ["NoDefaultRole", / NoDefaultRole$/],
      ["NotAuthorized", / NotAuthorized$/],
      ["TransactionNotAllowed", / TransactionNotAllowed$/],
      ["SendNotAllowed", / SendNotAllowed$/],
      ["reentries refused", /^reentries refused$/],
      ["invalidate", /^invalidate$/],
      ["renounce", /^renounce$/],
      ["revoke", /^revoke$/],
      ["disable", /^disable$/],
    ]
    if (STEPS < FULL_STEPS || SEED !== FULL_SEED) return
    const missing = required
      .filter(([, re]) => reached(re) === 0)
      .map(([name]) => name)
    assert.deepEqual(
      missing,
      [],
      `outcomes never reached (ATTRIBUTION_STEPS=${STEPS}, ATTRIBUTION_SEED=${SEED})`
    )
  })
})
