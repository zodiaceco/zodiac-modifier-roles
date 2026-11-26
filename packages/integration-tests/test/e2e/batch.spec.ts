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
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import { randomBytes } from "node:crypto"
import { existsSync } from "node:fs"
import path from "node:path"
import { after, describe, it } from "node:test"
import { fileURLToPath } from "node:url"
import { network } from "hardhat"
import {
  bytesToHex,
  decodeErrorResult,
  encodeAbiParameters,
  encodeFunctionData,
  hexToBytes,
  parseAbi,
  toFunctionSelector,
  toHex,
} from "viem"
import type { Address, Hex } from "viem"

import { extractRevertData } from "../../../evm/test/utils.js"
import { safeAbi as abiSafe } from "../eip712/setup/safe-deployments/index.js"
import { deploySafe } from "../eip712/setup/safe.js"
import deployMastercopies from "../eip712/setup/deploy-mastercopies/index.js"
import {
  count,
  deployMultiSend,
  deployRoles,
  execSafe,
  packMultiSend,
  prng,
} from "./helpers.js"

const here = path.dirname(fileURLToPath(import.meta.url))
const LEAN_BIN = path.resolve(
  here,
  "../../../evm/formal/.lake/build/bin/roles-model"
)

const connection = await network.create()
const { viem } = connection

const CASES = Number(process.env.BATCH_CASES ?? 200)
const { rnd, int, pick, chance } = prng(Number(process.env.BATCH_SEED ?? 1))

const fnAbi = parseAbi([
  "function fn(uint256 a, uint256 b, uint256[] arr)",
  "function other(uint256 x)",
  "function multiSend(bytes transactions)",
])
const FN = toFunctionSelector("fn(uint256,uint256,uint256[])")
const OTHER = toFunctionSelector("other(uint256)")
const MULTISEND = toFunctionSelector("multiSend(bytes)")

/* Conditions, as the contract stores them (BFS flattened by hand). */
type Node = {
  paramType: number
  operator: number
  compValue?: Hex
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
const word = (v: number | bigint): Hex =>
  encodeAbiParameters([{ type: "uint256" }], [BigInt(v)])

function flatten(root: Node) {
  const out: {
    parent: number
    paramType: number
    operator: number
    compValue: Hex
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
function staticCond(keys: Hex[]): Node {
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

function arrayCond(keys: Hex[]): Node {
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
function fnCond(keys: Hex[]): Node {
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

function otherCond(keys: Hex[]): Node {
  return {
    paramType: E.AbiEncoded,
    operator: O.Matches,
    children: [staticCond(keys)],
  }
}

const PASS: Node = { paramType: E.None, operator: O.Pass }

type Tx = { op: number; to: Address; value: bigint; data: Hex }

function randomData(): Hex {
  const r = rnd()
  if (r < 0.8)
    return encodeFunctionData({
      abi: fnAbi,
      functionName: "fn",
      args: [
        BigInt(int(8)),
        BigInt(int(8)),
        Array.from({ length: int(4) }, () => BigInt(int(8))),
      ],
    })
  if (r < 0.95)
    return encodeFunctionData({
      abi: fnAbi,
      functionName: "other",
      args: [BigInt(int(8))],
    })
  if (r < 0.98) return "0x"
  return "0x1234"
}

const packBatch = (txs: Tx[]) =>
  packMultiSend(txs.map(({ op, ...t }) => ({ ...t, operation: op })))

function mutateBatch(data: Hex): Hex {
  const b = hexToBytes(data)
  if (chance(0.5)) {
    const i = 4 + int(Math.max(1, b.length - 4))
    b[i] = int(256)
    return bytesToHex(b)
  }
  return bytesToHex(b.slice(0, 4 + int(Math.max(1, b.length - 4))))
}

function lean(line: string): string {
  const res = spawnSync(LEAN_BIN, [], { input: line + "\n", encoding: "utf8" })
  if (res.status !== 0) throw new Error(`lean driver failed: ${res.stderr}`)
  return res.stdout.trim()
}

describe("batches on chain: Roles authorizes and settles as the Lean batch model", () => {
  after(async () => {
    await connection.close()
  })

  it(`calls and MultiSend batches through a role (${CASES} cases)`, async (t) => {
    if (!existsSync(LEAN_BIN)) {
      t.skip()
      return
    }

    await deployMastercopies(viem)
    const [owner, member] = await viem.getWalletClients()
    const publicClient = await viem.getPublicClient()
    const safe = await deploySafe(
      {
        owners: [owner.account.address],
        threshold: 1,
        creationNonce: BigInt(toHex(randomBytes(32))),
      },
      owner
    )
    const roles = await deployRoles(viem, owner.account.address, safe)
    await execSafe(
      owner,
      safe,
      safe,
      encodeFunctionData({
        abi: abiSafe,
        functionName: "enableModule",
        args: [roles.address],
      })
    )
    await owner.sendTransaction({ to: safe, value: 10n ** 18n })
    const msAddr = (
      await deployMultiSend(viem, roles, owner)
    ).toLowerCase() as Address

    const tally: Record<string, number> = {}
    const refusals: Record<string, number> = {}
    for (let i = 0; i < CASES; i++) {
      const role = toHex(randomBytes(32))
      await roles.write.grantRole([member.account.address, role, 0n, 0n, 0n], {
        account: owner.account,
      })
      const keys = [0, 1, 2].map(() => toHex(randomBytes(32)))
      const balances = keys.map(() => BigInt(int(40)))
      for (let k = 0; k < keys.length; k++)
        await roles.write.setAllowance([keys[k], balances[k], 0n, 0n, 0n, 0n], {
          account: owner.account,
        })

      // permissions on two targets, and sometimes a global one
      const targets = [0, 1, 2].map(
        () => toHex(randomBytes(20)).toLowerCase() as Address
      )
      const perms: string[] = []
      try {
        for (const target of targets.slice(0, 2)) {
          const options = int(4)
          const r = rnd()
          const mode = r < 0.4 ? 0 : r < 0.9 ? 1 : 2
          if (mode === 0) {
            const tree = chance(0.5) ? PASS : fnCond(keys)
            const flat = flatten(tree)
            await roles.write.allowTarget([role, target, flat, options], {
              account: owner.account,
            })
            perms.push(`${target}/*/${options}/${leanNodes(flat)}`)
          } else if (mode === 1) {
            await roles.write.scopeTarget([role, target], {
              account: owner.account,
            })
            const flat = flatten(fnCond(keys))
            await roles.write.allowFunction([role, target, FN, flat, options], {
              account: owner.account,
            })
            perms.push(`${target}/${FN}/${options}/${leanNodes(flat)}`)
            if (chance(0.7)) {
              const flat2 = flatten(chance(0.5) ? PASS : otherCond(keys))
              await roles.write.allowFunction(
                [role, target, OTHER, flat2, options],
                { account: owner.account }
              )
              perms.push(`${target}/${OTHER}/${options}/${leanNodes(flat2)}`)
            }
          }
        }
        if (chance(0.3)) {
          const flat = flatten(otherCond(keys))
          await roles.write.allowFunctionGlobally([role, OTHER, flat], {
            account: owner.account,
          })
          perms.push(`g/${OTHER}/0/${leanNodes(flat)}`)
        }
      } catch (e: unknown) {
        // a tree the contract's integrity check rejects: the test's bug
        const msg =
          e instanceof Error
            ? ((e as { shortMessage?: string }).shortMessage ?? e.message)
            : String(e)
        throw new Error(`permission setup failed: ${msg}`)
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
        let data = encodeFunctionData({
          abi: fnAbi,
          functionName: "multiSend",
          args: [packBatch(Array.from({ length: n }, entry))],
        })
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
      assert.notEqual(model, "bad-input", `driver output for ${tx.data}`)

      let ok = true
      let reason = ""
      try {
        const hash = await roles.write.execTransactionWithRole(
          [tx.to, tx.value, tx.data, tx.op, role],
          { account: member.account, gas: 10_000_000n }
        )
        await publicClient.waitForTransactionReceipt({ hash })
      } catch (e: unknown) {
        ok = false
        const raw = extractRevertData(e) ?? ""
        try {
          const err =
            raw.length >= 10
              ? decodeErrorResult({ abi: roles.abi, data: raw as Hex })
              : null
          reason =
            err?.errorName === "ConditionViolation"
              ? `status ${err.args?.[0]}`
              : (err?.errorName ?? `unparsed ${raw.slice(0, 10)}`)
        } catch {
          const msg =
            e instanceof Error
              ? ((e as { shortMessage?: string }).shortMessage ?? e.message)
              : String(e)
          reason = `unparsed ${raw.slice(0, 10) || msg.slice(0, 80)}`
        }
      }

      const ctx = `case ${i}: ${JSON.stringify({ tx: { ...tx, value: String(tx.value) }, perms, balances: balances.map(String) })}`
      assert.equal(ok, model !== "none", `${ctx}\nmodel: ${model}`)
      // when the model refuses, Roles' authorization must be what refuses:
      // not the executed call (ModuleTransactionFailed), not out of gas
      if (!ok)
        assert.doesNotMatch(
          reason,
          /^(unparsed|ModuleTransactionFailed$)/,
          `${ctx}\nrefused, but not by Roles`
        )
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
        const stored = (await roles.read.allowances([keys[k]]))[3]
        const expected = balances[k] - (consumed.get(keys[k]) ?? 0n)
        assert.equal(stored, expected, `${ctx}\nmodel: ${model}\nkey ${k}`)
        if (consumed.has(keys[k])) count(tally, "keys charged")
      }
    }
    console.log("batches", tally, refusals)
    for (const k of ["single through", "batch through", "keys charged"])
      assert.ok((tally[k] ?? 0) > 0, `${k} never reached`)
    assert.ok(
      Object.keys(refusals).some((r) => r.startsWith("status ")),
      "no condition ever refused"
    )
  })
})
