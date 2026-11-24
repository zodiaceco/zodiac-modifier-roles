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
import { expect } from "chai"
import {
  AbiCoder,
  Interface,
  concat,
  getBytes,
  hexlify,
  keccak256,
  randomBytes,
  toBeHex,
} from "ethers"
import type { Signer } from "ethers"
import { network } from "hardhat"

import { iface as ifaceSafe } from "../eip712/setup/deploy-mastercopies/safeMastercopy.js"
import deployMastercopies from "../eip712/setup/deploy-mastercopies/index.js"
import { count, prng, safeWithRoles } from "./helpers.js"

import { calldataMatches } from "../../../sdk/src/main/target/authoring/c/matches.js"
import { or } from "../../../sdk/src/main/target/authoring/c/branching.js"
import {
  encodeTypedDomain,
  encodeTypedMessage,
  toAbiTypes,
} from "../../../sdk/src/main/eip712-signer/encode/index.js"
import { normalizeCondition } from "../../../sdk/src/main/condition/normalize/index.js"
import { flattenCondition } from "../../../sdk/src/main/condition/flattenCondition.js"
// from the built package: its source imports a module with top-level await,
// which cannot be loaded from here
import { allowSignTypedMessage } from "zodiac-roles-sdk"

const connection = await network.create()
const { ethers } = connection
const abi = AbiCoder.defaultAbiCoder()

const CASES = Number(process.env.PIN_CASES ?? 300)
const SAFE_MSG_TYPEHASH =
  "0x60b3cbf8b4a223d68d641b3b6ddf9a298e7f33710cf3d3a9d1146b5a6150fbca"
const libIface = new Interface([
  "function signMessage(bytes message)",
  "event SignMsg(bytes32 indexed msgHash)",
])
const safeIface = new Interface([
  "function signedMessages(bytes32) view returns (uint256)",
])

const { rnd, int, pick } = prng(Number(process.env.PIN_SEED ?? 1))
/** Outcomes that are neither a stored key nor a refusal by Roles or the
 *  library: out of gas, a revert without data, a call that stored nothing. */
const unexpected = (t: Record<string, number>) =>
  Object.keys(t).filter((k) => !["stored", "roles", "library"].includes(k))
const bytesOf = (n: number) =>
  hexlify(Uint8Array.from({ length: n }, () => int(256)))

const flat = (condition: any) =>
  flattenCondition(normalizeCondition(condition)).map((c) => ({
    parent: c.parent,
    paramType: c.paramType,
    operator: c.operator,
    compValue: c.compValue ?? "0x",
  }))

/** Calldata mutations: where Roles' and the library's readers could part. */
function mutate(base: string, decoys: string[]): string {
  const b = getBytes(base)
  const word = (x: number | bigint) => getBytes(toBeHex(x, 32))
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
        const decoy = getBytes(pick(decoys))
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
        const pointer = BigInt(hexlify(out.slice(h, h + 32)))
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
        const junk = getBytes(bytesOf(int(96)))
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
  return hexlify(out)
}

describe("signing routes on chain: Roles' pins restrict what the library signs", () => {
  after(async () => {
    await connection.close()
  })

  async function setup() {
    await deployMastercopies(ethers)
    const [owner, member] = await ethers.getSigners()
    const lib = await (
      await ethers.getContractFactory("SignTypedMessageLib")
    ).deploy()
    const libAddr = await lib.getAddress()
    const encoder = await (
      await ethers.getContractFactory("MockEIP712Encoder")
    ).deploy()
    const { safe, roles } = await safeWithRoles(ethers, owner)
    const ds = abi.decode(
      ["bytes32"],
      await owner.call({
        to: safe,
        data: ifaceSafe.encodeFunctionData("domainSeparator"),
      })
    )[0] as string
    const key = (message: string) =>
      keccak256(
        concat([
          "0x1901",
          ds,
          keccak256(
            abi.encode(
              ["bytes32", "bytes32"],
              [SAFE_MSG_TYPEHASH, keccak256(message)]
            )
          ),
        ])
      )
    const role = hexlify(randomBytes(32))
    await roles.grantRole(await member.getAddress(), role, 0, 0, 0)
    await roles.scopeTarget(role, libAddr)
    /** The Safe has the key signed: `signedMessages(key) == 1`. */
    const signedBySafe = async (k: string) =>
      BigInt(
        await ethers.provider.call({
          to: safe,
          data: safeIface.encodeFunctionData("signedMessages", [k]),
        })
      ) === 1n
    return {
      roles,
      member,
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
    roles: any,
    member: Signer,
    libAddr: string,
    role: string,
    data: string
  ): Promise<{ key?: string; refused?: string }> {
    try {
      const tx = await roles
        .connect(member)
        .execTransactionWithRole(libAddr, 0, data, 1, role, {
          gasLimit: 3_000_000,
        })
      const receipt = await tx.wait()
      const log = receipt.logs.find(
        (l: any) => l.topics[0] === libIface.getEvent("SignMsg")!.topicHash
      )
      if (!log) return { refused: "other: succeeded without SignMsg" }
      return { key: log.topics[1] }
    } catch (e: any) {
      const raw: string =
        typeof e.data === "string"
          ? e.data
          : (e.data?.data ?? e.info?.error?.data ?? "")
      const sel = typeof raw === "string" ? raw.slice(0, 10) : ""
      const rolesErr = sel ? roles.interface.getError(sel) : null
      // the library's revert reaches us wrapped by Roles; anything else
      // (a Panic, an unknown selector, no data) is unexpected
      if (rolesErr?.name === "ModuleTransactionFailed")
        return { refused: "library" }
      if (rolesErr) return { refused: "roles" }
      return {
        refused: `other: ${sel || String(e.shortMessage ?? e.message).slice(0, 80)}`,
      }
    }
  }

  it(`signMessage: a stored key is a pinned message's (${CASES} calls)`, async function () {
    this.timeout(0)
    const { roles, member, libAddr, key, role, signedBySafe } = await setup()
    const lens = [0, 1, 31, 32, 33, 64, 100]
    const pinned = [bytesOf(pick(lens)), bytesOf(pick(lens))]
    await roles.allowFunction(
      role,
      libAddr,
      libIface.getFunction("signMessage")!.selector,
      flat(calldataMatches([or(pinned[0], pinned[1])], ["bytes"])()),
      2
    )
    const keys = pinned.map(key)
    const decoys = [...pinned, bytesOf(40), "0x"]
      .map(
        (m) => abi.encode(["bytes"], [m]).slice(66) // length word and content
      )
      .map((x) => "0x" + x)

    const tally = { stored: 0, roles: 0, library: 0 }
    for (let i = 0; i < CASES; i++) {
      const m = rnd() < 0.7 ? pick(pinned) : bytesOf(pick(lens))
      const base = libIface.encodeFunctionData("signMessage", [m])
      const data = rnd() < 0.2 ? base : mutate(base, decoys)
      const r = await run(roles, member, libAddr, role, data)
      if (r.key) {
        tally.stored++
        expect(keys, `stored key for ${data}`).to.include(r.key)
        expect(await signedBySafe(r.key), `signed ${r.key}`).to.equal(true)
      } else count(tally, r.refused!)
    }
    console.log("signMessage", tally)
    expect(tally.stored).to.be.greaterThan(0)
    expect(tally.roles, "Roles never refused").to.be.greaterThan(0)
    expect(unexpected(tally), "unexpected outcomes").to.deep.equal([])
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
    { roles, libAddr, role }: Awaited<ReturnType<typeof setup>>,
    types: any,
    message: any
  ) {
    const domain = {
      chainId: 1,
      verifyingContract: libAddr as `0x${string}`,
    }
    const permission = allowSignTypedMessage({
      types,
      domain: { chainId: 1n, verifyingContract: libAddr } as any,
      message: {} as any,
    })
    await roles.allowFunction(
      role,
      libAddr,
      permission.selector,
      flat(permission.condition),
      2
    )
    const pinnedDomain = encodeTypedDomain({ domain, types })
    const pinnedTypes = toAbiTypes({ types }).map(
      (n: any) => [n.parent, n.encoding, n.typeHash] as const
    )
    const signTyped = new Interface([
      "function signTypedMessage(bytes domain, bytes message, (uint256 parent, uint8 encoding, bytes32 typeHash)[] types)",
    ])
    const base =
      permission.selector +
      signTyped
        .encodeFunctionData("signTypedMessage", [
          pinnedDomain,
          encodeTypedMessage({ types, message } as any),
          pinnedTypes,
        ])
        .slice(10)
    return { domain, pinnedDomain, pinnedTypes, base }
  }

  for (const [name, { types, message }] of Object.entries(TYPED))
    it(`signTypedMessage (${name}): the library hashes the pinned domain and types (${CASES} calls)`, async function () {
      this.timeout(0)
      const ctx = await setup()
      const { roles, member, libAddr, encoder, key, role, signedBySafe } = ctx
      const { domain, pinnedDomain, pinnedTypes, base } = await allowTyped(
        ctx,
        types,
        message
      )
      const decoys = [
        // a types array with a different message type hash
        "0x" +
          abi
            .encode(
              ["tuple(uint256,uint8,bytes32)[]"],
              [
                pinnedTypes.map(([p, e, h], i) => [
                  p,
                  e,
                  i === 1 ? keccak256("0x01") : h,
                ]),
              ]
            )
            .slice(66),
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
        const r = await run(roles, member, libAddr, role, data)
        if (!r.key) {
          count(tally, r.refused!)
          continue
        }
        tally.stored++
        const d = getBytes(data)
        const load = (p: number) =>
          BigInt(
            hexlify(Uint8Array.from({ length: 32 }, (_, k) => d[p + k] ?? 0))
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
          return hexlify(d.slice(Number(off), Number(off + len)))
        }
        const [a0, a1] = [arg(0), arg(1)]
        expect(
          a0 !== undefined && a1 !== undefined,
          `stored a key for arguments outside the calldata: ${data}`
        ).to.equal(true)
        // whatever domain the calldata carries, the key is the pinned one's
        const digest = await encoder.hashTypedMessage(
          pinnedDomain,
          a1!,
          pinnedTypes as any
        )
        expect(r.key, `stored key for ${data}`).to.equal(key(digest))
        expect(await signedBySafe(r.key!), `signed ${r.key}`).to.equal(true)
      }
      console.log(`signTypedMessage (${name})`, tally)
      expect(tally.stored).to.be.greaterThan(0)
      expect(tally.roles, "Roles never refused").to.be.greaterThan(0)
      expect(unexpected(tally), "unexpected outcomes").to.deep.equal([])
    })

  // Roles checks only what a condition walks: under `Pass` (the message is
  // free) it does not read a nested struct's head. The library hashes the
  // whole message, so it refuses a malformed field there: nothing is signed.
  it("signTypedMessage: a malformed field the condition leaves free is refused by the library", async () => {
    const ctx = await setup()
    const { roles, member, libAddr, role } = ctx
    const { types, message } = TYPED["nested, with an array"]
    const { base } = await allowTyped(ctx, types, message)
    const send = (data: string) =>
      roles.connect(member).execTransactionWithRole(libAddr, 0, data, 1, role)

    // message -> Order head: amount, maker's offset; maker's head: name's offset
    const d = getBytes(base)
    const word = (at: number) => Number(BigInt(hexlify(d.slice(at, at + 32))))
    const messageAt = 4 + word(4 + 32) + 32
    const makerAt = messageAt + word(messageAt + 32)
    // maker.name's offset, far past the end
    d.set(getBytes(toBeHex(2n ** 200n + 0x40n, 32)), makerAt)

    await expect(send(hexlify(d)))
      .to.be.revertedWithCustomError(roles, "ModuleTransactionFailed")
      .withArgs(
        new Interface(["error InvalidEIP712Encoding()"]).encodeErrorResult(
          "InvalidEIP712Encoding"
        )
      )
    // the same call, well formed, is signed
    await expect(send(base)).to.not.be.revert(ethers)
  })
})
