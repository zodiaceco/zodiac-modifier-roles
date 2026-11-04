/**
 * Batches on chain against the Lean batch model (packages/evm/formal/EndToEnd,
 * `Batch.lean`): a real Safe 1.4.1, the v3 Roles, MultiSend and
 * MultiSendUnwrapper.
 *
 * Each case gives a role random permissions (target-wide, per function,
 * global) whose conditions charge a few allowances: on parameters, on
 * array elements, on the ether value, per call, in `Or` branches that fail
 * after charging, and twice in one `And`. Then the role sends one call or
 * a MultiSend batch (sometimes malformed). The Lean driver runs
 * `EndToEnd.authorize` on the same input. The test compares:
 * - whether Roles lets the call through, and
 * - every allowance's stored balance afterwards: the balance minus what
 *   the model's consumption list charged to it (or unchanged).
 *
 * That is where the Solidity could part from the model: the consumption
 * list is threaded through memory (copy on write, shared entries), across
 * the transactions of a batch, and `_persist` writes every entry.
 */
import { expect } from "chai"
import { spawnSync } from "node:child_process"
import { existsSync } from "node:fs"
import path from "node:path"
import { fileURLToPath } from "node:url"
import {
  AbiCoder,
  Interface,
  ZeroAddress,
  ZeroHash,
  concat,
  getBytes,
  hexlify,
  randomBytes,
  solidityPacked,
  toBeHex,
} from "ethers"
import type { Signer } from "ethers"
import { network } from "hardhat"

import { iface as ifaceSafe } from "../eip712/setup/deploy-mastercopies/safeMastercopy.js"
import { deploySafe } from "../eip712/setup/safe.js"
import deployMastercopies from "../eip712/setup/deploy-mastercopies/index.js"

const here = path.dirname(fileURLToPath(import.meta.url))
const LEAN_BIN = path.resolve(
  here,
  "../../../evm/formal/.lake/build/bin/roles-model"
)

const connection = await network.create()
const { ethers } = connection
const abi = AbiCoder.defaultAbiCoder()

const CASES = Number(process.env.BATCH_CASES ?? 200)
let seed = Number(process.env.BATCH_SEED ?? 1)
const rnd = () => {
  seed = (seed * 1103515245 + 12345) % 2 ** 31
  return seed / 2 ** 31
}
const pick = <T>(xs: T[]): T => xs[Math.floor(rnd() * xs.length)]
const int = (n: number) => Math.floor(rnd() * n)
const chance = (p: number) => rnd() < p
const count = (t: Record<string, number>, k: string) => {
  t[k] = (t[k] ?? 0) + 1
}

const fnIface = new Interface([
  "function fn(uint256 a, uint256 b, uint256[] arr)",
  "function other(uint256 x)",
  "function multiSend(bytes transactions)",
])
const FN = fnIface.getFunction("fn")!.selector
const OTHER = fnIface.getFunction("other")!.selector

/* Conditions, as the contract stores them (BFS flattened by hand). */
type Node = {
  paramType: number
  operator: number
  compValue?: string
  children?: Node[]
}
const E = { None: 0, Static: 1, Array: 4, AbiEncoded: 5, EtherValue: 6 }
const O = {
  Pass: 0,
  And: 1,
  Or: 2,
  Matches: 5,
  ArraySome: 6,
  ArrayEvery: 7,
  EqualTo: 16,
  GreaterThan: 17,
  WithinAllowance: 28,
  CallWithinAllowance: 30,
}
const word = (v: number | bigint) => abi.encode(["uint256"], [v])

function flatten(root: Node) {
  const out: {
    parent: number
    paramType: number
    operator: number
    compValue: string
  }[] = []
  const queue: { node: Node; parent: number }[] = [{ node: root, parent: 0 }]
  while (queue.length) {
    const { node, parent } = queue.shift()!
    const i = out.length
    out.push({
      parent,
      paramType: node.paramType,
      operator: node.operator,
      compValue: node.compValue ?? "0x",
    })
    for (const c of node.children ?? []) queue.push({ node: c, parent: i })
  }
  return out
}
const leanNodes = (flat: ReturnType<typeof flatten>) =>
  flat
    .map((n) => `${n.parent}:${n.paramType}:${n.operator}:${n.compValue}`)
    .join("|")

/** A condition on a `uint256`: allowances in every arrangement that matters. */
function staticCond(keys: string[]): Node {
  const wa = (k = pick(keys)): Node => ({
    paramType: E.Static,
    operator: O.WithinAllowance,
    compValue: k,
  })
  const eq = (): Node => ({
    paramType: E.Static,
    operator: O.EqualTo,
    compValue: word(int(6)),
  })
  const gt = (): Node => ({
    paramType: E.Static,
    operator: O.GreaterThan,
    compValue: word(int(3)),
  })
  const or = (...children: Node[]): Node => ({
    paramType: E.None,
    operator: O.Or,
    children,
  })
  const and = (...children: Node[]): Node => ({
    paramType: E.None,
    operator: O.And,
    children,
  })
  switch (int(9)) {
    case 0:
      return { paramType: E.Static, operator: O.Pass }
    case 1:
    case 2:
      return wa()
    case 3:
      return or(wa(), wa())
    case 4: {
      // the same allowance charged twice
      const k = pick(keys)
      return and(wa(k), wa(k))
    }
    case 5:
      // a branch that charges and then fails
      return or(and(wa(), eq()), wa())
    case 6:
      return or(and(wa(), gt()), { paramType: E.Static, operator: O.Pass })
    case 7:
      return and(gt(), wa())
    default:
      return chance(0.5) ? eq() : { paramType: E.Static, operator: O.Pass }
  }
}

function arrayCond(keys: string[]): Node {
  const el = staticCond(keys)
  switch (int(4)) {
    case 0:
      return {
        paramType: E.Array,
        operator: O.Pass,
        children: [{ paramType: E.Static, operator: O.Pass }],
      }
    case 1:
      return { paramType: E.Array, operator: O.ArraySome, children: [el] }
    case 2:
      return { paramType: E.Array, operator: O.ArrayEvery, children: [el] }
    default:
      return {
        paramType: E.Array,
        operator: O.Matches,
        children: [el, staticCond(keys)],
      }
  }
}

/** A condition on `fn(uint256,uint256,uint256[])`, with the ether value or
 *  the call metered next to it sometimes. */
function fnCond(keys: string[]): Node {
  const matches: Node = {
    paramType: E.AbiEncoded,
    operator: O.Matches,
    children: [staticCond(keys), staticCond(keys), arrayCond(keys)],
  }
  const extra: Node[] = []
  if (chance(0.3))
    extra.push({
      paramType: E.EtherValue,
      operator: O.WithinAllowance,
      compValue: pick(keys),
    })
  if (chance(0.3))
    extra.push({
      paramType: E.None,
      operator: O.CallWithinAllowance,
      compValue: pick(keys),
    })
  return extra.length
    ? { paramType: E.None, operator: O.And, children: [matches, ...extra] }
    : matches
}

function otherCond(keys: string[]): Node {
  return {
    paramType: E.AbiEncoded,
    operator: O.Matches,
    children: [staticCond(keys)],
  }
}

const PASS: Node = { paramType: E.None, operator: O.Pass }

type Tx = { op: number; to: string; value: bigint; data: string }

function randomData(): string {
  const r = rnd()
  if (r < 0.8)
    return fnIface.encodeFunctionData("fn", [
      int(8),
      int(8),
      Array.from({ length: int(4) }, () => int(8)),
    ])
  if (r < 0.95) return fnIface.encodeFunctionData("other", [int(8)])
  if (r < 0.98) return "0x"
  return "0x1234"
}

const packBatch = (txs: Tx[]) =>
  concat(
    txs.map((t) =>
      solidityPacked(
        ["uint8", "address", "uint256", "uint256", "bytes"],
        [t.op, t.to, t.value, getBytes(t.data).length, t.data]
      )
    )
  )

function mutateBatch(data: string): string {
  const b = getBytes(data)
  if (chance(0.5)) {
    const i = 4 + int(Math.max(1, b.length - 4))
    b[i] = int(256)
    return hexlify(b)
  }
  return hexlify(b.slice(0, 4 + int(Math.max(1, b.length - 4))))
}

function lean(line: string): string {
  const res = spawnSync(LEAN_BIN, [], { input: line + "\n", encoding: "utf8" })
  if (res.status !== 0) throw new Error(`lean driver failed: ${res.stderr}`)
  return res.stdout.trim()
}

async function deployRoles(owner: string, avatar: string) {
  const lib = async (name: string) =>
    (await (await ethers.getContractFactory(name)).deploy()).getAddress()
  const libraries = {
    ConditionStorer: await lib("ConditionStorer"),
    WithinRatioChecker: await lib("WithinRatioChecker"),
    CustomConditionChecker: await lib("CustomConditionChecker"),
  }
  return (await ethers.getContractFactory("Roles", { libraries })).deploy(
    owner,
    avatar,
    avatar
  )
}

async function execSafe(owner: Signer, safe: string, to: string, data: string) {
  const approval = concat([
    abi.encode(["address"], [await owner.getAddress()]),
    ZeroHash,
    "0x01",
  ])
  return owner.sendTransaction({
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
}

describe("batches on chain: Roles authorizes and settles as the Lean batch model", () => {
  after(async () => {
    await connection.close()
  })

  it(`calls and MultiSend batches through a role (${CASES} cases)`, async function () {
    if (!existsSync(LEAN_BIN)) this.skip()
    this.timeout(0)

    await deployMastercopies(ethers)
    const [owner, member] = await ethers.getSigners()
    const safe = await deploySafe(
      {
        owners: [await owner.getAddress()],
        threshold: 1,
        creationNonce: BigInt(hexlify(randomBytes(32))),
      },
      owner as any
    )
    const roles: any = await deployRoles(await owner.getAddress(), safe)
    await execSafe(
      owner,
      safe,
      safe,
      ifaceSafe.encodeFunctionData("enableModule", [await roles.getAddress()])
    )
    await owner.sendTransaction({ to: safe, value: 10n ** 18n })
    const multisend = await (
      await ethers.getContractFactory("MultiSend")
    ).deploy()
    const msAddr = (await multisend.getAddress()).toLowerCase()
    const unwrapper = await (
      await ethers.getContractFactory("MultiSendUnwrapper")
    ).deploy()
    const MULTISEND = fnIface.getFunction("multiSend")!.selector
    await roles.setTransactionUnwrapper(
      msAddr,
      MULTISEND,
      await unwrapper.getAddress()
    )

    const tally: Record<string, number> = {}
    const refusals: Record<string, number> = {}
    for (let i = 0; i < CASES; i++) {
      const role = hexlify(randomBytes(32))
      await roles.grantRole(await member.getAddress(), role, 0, 0, 0)
      const keys = [0, 1, 2].map(() => hexlify(randomBytes(32)))
      const balances = keys.map(() => BigInt(int(40)))
      for (let k = 0; k < keys.length; k++)
        await roles.setAllowance(keys[k], balances[k], 0, 0, 0, 0)

      // permissions on two targets, and sometimes a global one
      const targets = [0, 1, 2].map(() =>
        hexlify(randomBytes(20)).toLowerCase()
      )
      const perms: string[] = []
      try {
        for (const t of targets.slice(0, 2)) {
          const options = int(4)
          const r = rnd()
          const mode = r < 0.4 ? 0 : r < 0.9 ? 1 : 2
          if (mode === 0) {
            const tree = chance(0.5) ? PASS : fnCond(keys)
            const flat = flatten(tree)
            await roles.allowTarget(role, t, flat, options)
            perms.push(`${t}/*/${options}/${leanNodes(flat)}`)
          } else if (mode === 1) {
            await roles.scopeTarget(role, t)
            const flat = flatten(fnCond(keys))
            await roles.allowFunction(role, t, FN, flat, options)
            perms.push(`${t}/${FN}/${options}/${leanNodes(flat)}`)
            if (chance(0.7)) {
              const flat2 = flatten(chance(0.5) ? PASS : otherCond(keys))
              await roles.allowFunction(role, t, OTHER, flat2, options)
              perms.push(`${t}/${OTHER}/${options}/${leanNodes(flat2)}`)
            }
          }
        }
        if (chance(0.3)) {
          const flat = flatten(otherCond(keys))
          await roles.allowFunctionGlobally(role, OTHER, flat)
          perms.push(`g/${OTHER}/0/${leanNodes(flat)}`)
        }
      } catch (e: any) {
        // a tree the contract's integrity check rejects: the test's bug
        throw new Error(
          `permission setup failed: ${e.shortMessage ?? e.message}`
        )
      }

      // one call, or a batch
      const entry = (): Tx => ({
        op: chance(0.95) ? 0 : 1,
        to: chance(0.95) ? pick(targets.slice(0, 2)) : targets[2],
        value: chance(0.85) ? 0n : BigInt(1 + int(3)),
        data: randomData(),
      })
      let tx: Tx
      if (chance(0.65)) {
        const n = 1 + int(4)
        let data = fnIface.encodeFunctionData("multiSend", [
          packBatch(Array.from({ length: n }, entry)),
        ])
        if (chance(0.1)) data = mutateBatch(data)
        tx = chance(0.95)
          ? { op: 1, to: msAddr, value: 0n, data }
          : { op: 0, to: msAddr, value: 0n, data }
        count(tally, "batch")
      } else {
        tx = entry()
        count(tally, "single")
      }

      const model = lean(
        [
          "az",
          tx.value,
          tx.op,
          tx.to,
          tx.data,
          keys.map((k, j) => `${k}:${balances[j]}`).join(","),
          `${msAddr}:${MULTISEND}`,
          perms.length ? perms.join(";") : "-",
        ].join(" ")
      )
      expect(model, `driver output for ${tx.data}`).to.not.equal("bad-input")

      let ok = true
      let reason = ""
      try {
        await (
          await roles
            .connect(member)
            .execTransactionWithRole(
              tx.to,
              tx.value,
              tx.data,
              tx.op,
              role,
              true,
              {
                gasLimit: 10_000_000,
              }
            )
        ).wait()
      } catch (e: any) {
        ok = false
        const raw: string =
          typeof e.data === "string"
            ? e.data
            : (e.data?.data ?? e.info?.error?.data ?? "")
        try {
          const err = roles.interface.parseError(raw)
          reason =
            err?.name === "ConditionViolation"
              ? `status ${err.args[0]}`
              : (err?.name ?? "?")
        } catch {
          reason = "?"
        }
      }

      const ctx = `case ${i}: ${JSON.stringify({ tx: { ...tx, value: String(tx.value) }, perms, balances: balances.map(String) })}`
      expect(ok, `${ctx}\nmodel: ${model}`).to.equal(model !== "none")
      count(tally, ok ? "through" : "refused")
      if (!ok) count(refusals, reason)
      else count(tally, tx.to === msAddr ? "batch through" : "single through")

      const consumed = new Map<string, bigint>()
      if (ok && model !== "-")
        for (const e of model.split(",")) {
          const [key, , used] = e.split(":")
          consumed.set("0x" + key, BigInt(used))
        }
      for (let k = 0; k < keys.length; k++) {
        const stored = (await roles.allowances(keys[k])).balance as bigint
        const expected = balances[k] - (consumed.get(keys[k]) ?? 0n)
        expect(stored, `${ctx}\nmodel: ${model}\nkey ${k}`).to.equal(expected)
        if (consumed.has(keys[k])) count(tally, "keys charged")
      }
    }
    console.log("batches", tally, refusals)
    expect(tally.through ?? 0).to.be.greaterThan(0)
    expect(tally["keys charged"] ?? 0).to.be.greaterThan(0)
  })
})
