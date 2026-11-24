/**
 * The signing routes (packages/evm/formal/EndToEnd, `route_bytes`,
 * `route_types`) on chain, with a real Safe 1.4.1, the v3 Roles and
 * SignTypedMessageLib, on random and malformed calldata.
 *
 * A role may only sign pinned messages (`signMessage`), or typed messages
 * with pinned `types`. For each call Roles lets through and the library
 * executes, the key the library stores must be:
 * - `signMessage`: the key of one of the pinned messages;
 * - `signTypedMessage`: the key of the digest the encoder computes with the
 *   pinned `types` (and the `domain` / `message` the fallback reads).
 *
 * The mutations move offsets, lengths and padding, add copies of other
 * values the offsets can point at, and truncate or extend the calldata:
 * where Roles' reader and the library's could disagree.
 */
import assert from "node:assert/strict"
import { randomBytes } from "node:crypto"
import { after, describe, it } from "node:test"
import { network } from "hardhat"
import {
  bytesToHex,
  concat,
  decodeErrorResult,
  encodeAbiParameters,
  encodeErrorResult,
  encodeFunctionData,
  hexToBytes,
  keccak256,
  parseAbi,
  parseAbiParameters,
  parseEventLogs,
  toFunctionSelector,
  toHex,
} from "viem"
import type { Address, Hex, WalletClient } from "viem"

import { extractRevertData } from "../../../evm/test/utils.js"
import type { RolesContract } from "../../../evm/test/utils.js"
import deployMastercopies from "../eip712/setup/deploy-mastercopies/index.js"
import { count, prng, safeWithRoles } from "./helpers.js"

import {
  __integration,
  allowSignTypedMessage,
  c,
  flattenCondition,
  normalizeCondition,
} from "zodiac-roles-sdk"

const { encodeTypedDomain, encodeTypedMessage, toAbiTypes } = __integration

const connection = await network.create()
const { viem } = connection

const CASES = Number(process.env.PIN_CASES ?? 300)
const SAFE_MSG_TYPEHASH =
  "0x60b3cbf8b4a223d68d641b3b6ddf9a298e7f33710cf3d3a9d1146b5a6150fbca" as const
const libAbi = parseAbi([
  "function signMessage(bytes message)",
  "event SignMsg(bytes32 indexed msgHash)",
])
const safeViewAbi = parseAbi([
  "function domainSeparator() view returns (bytes32)",
  "function signedMessages(bytes32) view returns (uint256)",
])
const signTypedAbi = parseAbi([
  "function signTypedMessage(bytes domain, bytes message, (uint256 parent, uint8 encoding, bytes32 typeHash)[] types)",
])

const { rnd, int, pick } = prng(Number(process.env.PIN_SEED ?? 1))
/** Outcomes that are neither a stored key nor a refusal by Roles or the
 *  library: out of gas, a revert without data, a call that stored nothing. */
const unexpected = (t: Record<string, number>) =>
  Object.keys(t).filter((k) => !["stored", "roles", "library"].includes(k))
const bytesOf = (n: number): Hex =>
  bytesToHex(Uint8Array.from({ length: n }, () => int(256)))

const flat = (condition: any) =>
  flattenCondition(normalizeCondition(condition)).map((c) => ({
    parent: c.parent,
    paramType: c.paramType,
    operator: c.operator,
    compValue: (c.compValue ?? "0x") as Hex,
  }))

/** Calldata mutations: where Roles' and the library's readers could part. */
function mutate(base: Hex, decoys: Hex[]): Hex {
  const b = hexToBytes(base)
  const word = (x: number | bigint) => hexToBytes(toHex(x, { size: 32 }))
  const head = (i: number) => 4 + 32 * i
  let out = Uint8Array.from(b)
  const set = (at: number, w: Uint8Array) => {
    if (at + 32 > out.length) {
      const grown = new Uint8Array(at + 32)
      grown.set(out)
      out = grown
    }
    out.set(w, at)
  }
  for (let k = 0, n = 1 + int(3); k < n; k++) {
    switch (int(8)) {
      case 0: {
        // point an argument at a decoy appended after the calldata
        const decoy = hexToBytes(pick(decoys))
        const at = out.length - 4
        const grown = new Uint8Array(out.length + decoy.length)
        grown.set(out)
        grown.set(decoy, out.length)
        out = grown
        set(head(int(3)), word(at))
        break
      }
      case 1:
        set(
          head(int(3)),
          word(pick([0, 1, 31, 32, 33, 64, 96, 2n ** 64n, 2n ** 255n]))
        )
        break
      case 2: {
        // change the length word of one of the arguments
        const h = head(int(3))
        if (h + 32 > out.length) break
        const pointer = BigInt(bytesToHex(out.slice(h, h + 32)))
        if (pointer + 36n > BigInt(out.length)) break
        set(
          Number(pointer) + 4,
          word(pick([0, 1, 31, 32, 33, 96, 2n ** 64n, 2n ** 256n - 1n]))
        )
        break
      }
      case 3:
        // dirty a byte (padding, content, element words)
        if (out.length > 4) out[4 + int(out.length - 4)] = int(256)
        break
      case 4:
        out = out.slice(0, 4 + int(Math.max(1, out.length - 4)))
        break
      case 5: {
        const junk = hexToBytes(bytesOf(int(96)))
        const grown = new Uint8Array(out.length + junk.length)
        grown.set(out)
        grown.set(junk, out.length)
        out = grown
        break
      }
      case 6:
        // swap two head words
        if (out.length >= 4 + 96) {
          const i = head(int(3)),
            j = head(int(3))
          const a = out.slice(i, i + 32),
            c = out.slice(j, j + 32)
          out.set(c, i)
          out.set(a, j)
        }
        break
      default:
        break // unchanged
    }
  }
  return bytesToHex(out)
}

describe("signing routes on chain: Roles' pins restrict what the library signs", () => {
  after(async () => {
    await connection.close()
  })

  async function setup() {
    await deployMastercopies(viem)
    const [owner, member] = await viem.getWalletClients()
    const publicClient = await viem.getPublicClient()
    const lib = await viem.deployContract("SignTypedMessageLib")
    const libAddr = lib.address
    const encoder = await viem.deployContract("MockEIP712Encoder")
    const { safe, roles } = await safeWithRoles(viem, owner)
    const ds = await publicClient.readContract({
      address: safe,
      abi: safeViewAbi,
      functionName: "domainSeparator",
    })
    const key = (message: Hex): Hex =>
      keccak256(
        concat([
          "0x1901",
          ds,
          keccak256(
            encodeAbiParameters(
              [{ type: "bytes32" }, { type: "bytes32" }],
              [SAFE_MSG_TYPEHASH, keccak256(message)]
            )
          ),
        ])
      )
    const role = toHex(randomBytes(32))
    await roles.write.grantRole([member.account.address, role, 0n, 0n, 0n], {
      account: owner.account,
    })
    await roles.write.scopeTarget([role, libAddr], { account: owner.account })
    /** The Safe has the key signed: `signedMessages(key) == 1`. */
    const signedBySafe = async (k: Hex) =>
      (await publicClient.readContract({
        address: safe,
        abi: safeViewAbi,
        functionName: "signedMessages",
        args: [k],
      })) === 1n
    return {
      roles,
      owner,
      member,
      publicClient,
      lib,
      libAddr,
      encoder,
      safe,
      key,
      role,
      signedBySafe,
    }
  }

  /** Runs `data` through Roles; the stored key, or why it was refused. */
  async function run(
    roles: RolesContract,
    member: WalletClient,
    publicClient: Awaited<ReturnType<typeof viem.getPublicClient>>,
    libAddr: Address,
    role: Hex,
    data: Hex
  ): Promise<{ key?: Hex; refused?: string }> {
    try {
      const hash = await roles.write.execTransactionWithRole(
        [libAddr, 0n, data, 1, role],
        { account: member.account!, gas: 3_000_000n }
      )
      const receipt = await publicClient.waitForTransactionReceipt({ hash })
      const logs = parseEventLogs({
        abi: libAbi,
        eventName: "SignMsg",
        logs: receipt.logs,
      })
      if (logs.length === 0)
        return { refused: "other: succeeded without SignMsg" }
      return { key: logs[0].args.msgHash }
    } catch (e: unknown) {
      const raw = extractRevertData(e) ?? ""
      const sel = raw.length >= 10 ? raw.slice(0, 10) : ""
      let rolesErrName: string | undefined
      if (sel) {
        try {
          rolesErrName = decodeErrorResult({
            abi: roles.abi,
            data: raw as Hex,
          }).errorName
        } catch {
          rolesErrName = undefined
        }
      }
      // the library's revert reaches us wrapped by Roles; anything else
      // (a Panic, an unknown selector, no data) is unexpected
      if (rolesErrName === "ModuleTransactionFailed")
        return { refused: "library" }
      if (rolesErrName) return { refused: "roles" }
      const msg =
        e instanceof Error
          ? ((e as { shortMessage?: string }).shortMessage ?? e.message)
          : String(e)
      return {
        refused: `other: ${sel || msg.slice(0, 80)}`,
      }
    }
  }

  it(`signMessage: a stored key is a pinned message's (${CASES} calls)`, async () => {
    const {
      roles,
      owner,
      member,
      publicClient,
      libAddr,
      key,
      role,
      signedBySafe,
    } = await setup()
    const lens = [0, 1, 31, 32, 33, 64, 100]
    const pinned = [bytesOf(pick(lens)), bytesOf(pick(lens))]
    await roles.write.allowFunction(
      [
        role,
        libAddr,
        toFunctionSelector("signMessage(bytes)"),
        flat(c.calldataMatches([c.or(pinned[0], pinned[1])], ["bytes"])()),
        2,
      ],
      { account: owner.account }
    )
    const keys = pinned.map(key)
    const decoys = [...pinned, bytesOf(40), "0x" as Hex].map(
      (m) =>
        ("0x" + encodeAbiParameters([{ type: "bytes" }], [m]).slice(66)) as Hex // length word and content
    )

    const tally = { stored: 0, roles: 0, library: 0 }
    for (let i = 0; i < CASES; i++) {
      const m = rnd() < 0.7 ? pick(pinned) : bytesOf(pick(lens))
      const base = encodeFunctionData({
        abi: libAbi,
        functionName: "signMessage",
        args: [m],
      })
      const data = rnd() < 0.2 ? base : mutate(base, decoys)
      const r = await run(roles, member, publicClient, libAddr, role, data)
      if (r.key) {
        tally.stored++
        assert.ok(keys.includes(r.key), `stored key for ${data}`)
        assert.equal(await signedBySafe(r.key), true, `signed ${r.key}`)
      } else count(tally, r.refused!)
    }
    console.log("signMessage", tally)
    assert.ok(tally.stored > 0)
    assert.ok(tally.roles > 0, "Roles never refused")
    assert.deepEqual(unexpected(tally), [], "unexpected outcomes")
  })

  /** Types for signTypedMessage, with a message of them. */
  const TYPED = {
    flat: {
      types: {
        EIP712Domain: [
          { name: "chainId", type: "uint256" },
          { name: "verifyingContract", type: "address" },
        ],
        Order: [
          { name: "amount", type: "uint256" },
          { name: "note", type: "string" },
        ],
      },
      message: { amount: 5n, note: "hello" },
    },
    "nested, with an array": {
      types: {
        EIP712Domain: [
          { name: "chainId", type: "uint256" },
          { name: "verifyingContract", type: "address" },
        ],
        Order: [
          { name: "amount", type: "uint256" },
          { name: "maker", type: "Person" },
          { name: "ids", type: "uint256[]" },
        ],
        Person: [
          { name: "name", type: "string" },
          { name: "wallet", type: "address" },
        ],
      },
      message: {
        amount: 5n,
        maker: {
          name: "alice",
          wallet: "0x00000000000000000000000000000000000000aa",
        },
        ids: [1n, 2n, 3n],
      },
    },
  } as const

  /** Allows the role the SDK's permission for `types`: domain pinned,
   *  message free, types pinned. Returns the call signing `message`. */
  async function allowTyped(
    { roles, owner, libAddr, role }: Awaited<ReturnType<typeof setup>>,
    types: any,
    message: any
  ) {
    const domain = {
      chainId: 1,
      verifyingContract: libAddr,
    }
    const permission = allowSignTypedMessage({
      types,
      domain: { chainId: 1n, verifyingContract: libAddr } as any,
      message: {} as any,
    })
    await roles.write.allowFunction(
      [
        role,
        libAddr,
        permission.selector as Hex,
        flat(permission.condition),
        2,
      ],
      { account: owner.account }
    )
    const pinnedDomain = encodeTypedDomain({ domain, types })
    const pinnedTypes = toAbiTypes({ types }).map((n) => ({
      parent: BigInt(n.parent),
      encoding: Number(n.encoding),
      typeHash: n.typeHash as Hex,
    }))
    const base = (permission.selector +
      encodeFunctionData({
        abi: signTypedAbi,
        functionName: "signTypedMessage",
        args: [
          pinnedDomain,
          encodeTypedMessage({ types, message } as any),
          pinnedTypes,
        ],
      }).slice(10)) as Hex
    return { domain, pinnedDomain, pinnedTypes, base }
  }

  for (const [name, { types, message }] of Object.entries(TYPED))
    it(`signTypedMessage (${name}): the library hashes the pinned domain and types (${CASES} calls)`, async () => {
      const ctx = await setup()
      const {
        roles,
        member,
        publicClient,
        libAddr,
        encoder,
        key,
        role,
        signedBySafe,
      } = ctx
      const { domain, pinnedDomain, pinnedTypes, base } = await allowTyped(
        ctx,
        types,
        message
      )
      const decoys: Hex[] = [
        // a types array with a different message type hash
        ("0x" +
          encodeAbiParameters(
            parseAbiParameters(
              "(uint256 parent, uint8 encoding, bytes32 typeHash)[]"
            ),
            [
              pinnedTypes.map((n, i) => ({
                ...n,
                typeHash: i === 1 ? keccak256("0x01") : n.typeHash,
              })),
            ]
          ).slice(66)) as Hex,
        // a domain with another chain id
        encodeTypedDomain({
          domain: { ...domain, chainId: 5 },
          types: types as any,
        }),
        bytesOf(64),
      ]

      const tally = { stored: 0, roles: 0, library: 0 }
      for (let i = 0; i < CASES; i++) {
        const data = rnd() < 0.2 ? base : mutate(base, decoys)
        const r = await run(roles, member, publicClient, libAddr, role, data)
        if (!r.key) {
          count(tally, r.refused!)
          continue
        }
        tally.stored++
        const d = hexToBytes(data)
        const load = (p: number) =>
          BigInt(
            bytesToHex(Uint8Array.from({ length: 32 }, (_, k) => d[p + k] ?? 0))
          )
        // The fallback takes `domain` and `message` offsets and lengths from
        // the calldata, and reverts unless they lie within it
        // (`SignTypedMessageLib._argument`): a stored key means they do.
        const size = BigInt(d.length)
        const arg = (j: number) => {
          const pointer = load(4 + 32 * j)
          if (size < 0x64n || pointer > size - 0x24n) return undefined
          const off = pointer + 0x24n
          const len = load(Number(pointer) + 4)
          if (len > size - off) return undefined
          return bytesToHex(d.slice(Number(off), Number(off + len)))
        }
        const [a0, a1] = [arg(0), arg(1)]
        assert.equal(
          a0 !== undefined && a1 !== undefined,
          true,
          `stored a key for arguments outside the calldata: ${data}`
        )
        // whatever domain the calldata carries, the key is the pinned one's
        const digest = await encoder.read.hashTypedMessage([
          pinnedDomain,
          a1!,
          pinnedTypes,
        ])
        assert.equal(r.key, key(digest), `stored key for ${data}`)
        assert.equal(await signedBySafe(r.key!), true, `signed ${r.key}`)
      }
      console.log(`signTypedMessage (${name})`, tally)
      assert.ok(tally.stored > 0)
      assert.ok(tally.roles > 0, "Roles never refused")
      assert.deepEqual(unexpected(tally), [], "unexpected outcomes")
    })

  // Roles checks only what a condition walks: under `Pass` (the message is
  // free) it does not read a nested struct's head. The library hashes the
  // whole message, so it refuses a malformed field there: nothing is signed.
  it("signTypedMessage: a malformed field the condition leaves free is refused by the library", async () => {
    const ctx = await setup()
    const { roles, member, libAddr, role } = ctx
    const { types, message } = TYPED["nested, with an array"]
    const { base } = await allowTyped(ctx, types, message)
    const send = (data: Hex) =>
      roles.write.execTransactionWithRole([libAddr, 0n, data, 1, role], {
        account: member.account,
      })

    // message -> Order head: amount, maker's offset; maker's head: name's offset
    const d = hexToBytes(base)
    const word = (at: number) =>
      Number(BigInt(bytesToHex(d.slice(at, at + 32))))
    const messageAt = 4 + word(4 + 32) + 32
    const makerAt = messageAt + word(messageAt + 32)
    // maker.name's offset, far past the end
    d.set(hexToBytes(toHex(2n ** 200n + 0x40n, { size: 32 })), makerAt)

    await viem.assertions.revertWithCustomErrorWithArgs(
      send(bytesToHex(d)),
      roles,
      "ModuleTransactionFailed",
      [
        encodeErrorResult({
          abi: parseAbi(["error InvalidEIP712Encoding()"]),
          errorName: "InvalidEIP712Encoding",
        }),
      ]
    )
    // the same call, well formed, is signed
    await send(base)
  })
})
