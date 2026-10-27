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
  ZeroAddress,
  ZeroHash,
  concat,
  getBytes,
  hexlify,
  keccak256,
  randomBytes,
  toBeHex,
  zeroPadValue,
} from "ethers"
import type { Signer } from "ethers"
import { network } from "hardhat"

import { iface as ifaceSafe } from "../eip712/setup/deploy-mastercopies/safeMastercopy.js"
import { deploySafe } from "../eip712/setup/safe.js"
import deployMastercopies from "../eip712/setup/deploy-mastercopies/index.js"

import { calldataMatches } from "../../../sdk/src/main/target/authoring/c/matches.js"
import { or } from "../../../sdk/src/main/target/authoring/c/branching.js"
import {
  encodeAbiTypes,
  encodeTypedDomain,
  encodeTypedMessage,
  toAbiTypes,
} from "../../../sdk/src/main/eip712-signer/encode/index.js"
import { normalizeCondition } from "../../../sdk/src/main/condition/normalize/index.js"
import { flattenCondition } from "../../../sdk/src/main/condition/flattenCondition.js"

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

let seed = Number(process.env.PIN_SEED ?? 1)
const rnd = () => {
  seed = (seed * 1103515245 + 12345) % 2 ** 31
  return seed / 2 ** 31
}
const pick = <T>(xs: T[]): T => xs[Math.floor(rnd() * xs.length)]
const int = (n: number) => Math.floor(rnd() * n)
const count = (t: Record<string, number>, k: string) => {
  t[k] = (t[k] ?? 0) + 1
}
const bytesOf = (n: number) =>
  hexlify(Uint8Array.from({ length: n }, () => int(256)))

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
        // change a length word
        const p = Number(BigInt(hexlify(out.slice(4, 36)))) + 4
        if (p + 32 <= out.length)
          set(p, word(pick([0, 1, 31, 32, 33, 96, 2n ** 64n, 2n ** 256n - 1n])))
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
    const safe = await deploySafe(
      {
        owners: [await owner.getAddress()],
        threshold: 1,
        creationNonce: BigInt(hexlify(randomBytes(32))),
      },
      owner as any
    )
    const roles = await deployRoles(await owner.getAddress(), safe)
    await execSafe(
      owner,
      safe,
      safe,
      ifaceSafe.encodeFunctionData("enableModule", [await roles.getAddress()])
    )
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
    return { roles, member, lib, libAddr, encoder, safe, key, role }
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
        .execTransactionWithRole(libAddr, 0, data, 1, role, true, {
          gasLimit: 3_000_000,
        })
      const receipt = await tx.wait()
      const log = receipt.logs.find(
        (l: any) => l.topics[0] === libIface.getEvent("SignMsg")!.topicHash
      )
      return { key: log?.topics[1] }
    } catch (e: any) {
      const raw: string =
        typeof e.data === "string"
          ? e.data
          : (e.data?.data ?? e.info?.error?.data ?? "")
      const sel = typeof raw === "string" ? raw.slice(0, 10) : ""
      if (sel === roles.interface.getError("ModuleTransactionFailed")!.selector)
        return { refused: "library" }
      if (sel === "")
        return {
          refused: "other:" + String(e.shortMessage ?? e.message).slice(0, 80),
        }
      return { refused: "roles" }
    }
  }

  it(`signMessage: a stored key is a pinned message's (${CASES} calls)`, async function () {
    this.timeout(0)
    const { roles, member, libAddr, key, role } = await setup()
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
      } else count(tally, r.refused!)
    }
    console.log("signMessage", tally)
    expect(tally.stored).to.be.greaterThan(0)
  })

  it(`signTypedMessage: the library hashes the pinned types (${CASES} calls)`, async function () {
    this.timeout(0)
    const { roles, member, libAddr, encoder, key, role } = await setup()
    const types = {
      EIP712Domain: [
        { name: "chainId", type: "uint256" },
        { name: "verifyingContract", type: "address" },
      ],
      Order: [
        { name: "amount", type: "uint256" },
        { name: "note", type: "string" },
      ],
    } as const
    const domain = { chainId: 1, verifyingContract: libAddr as `0x${string}` }
    const nodes = toAbiTypes({ domain, types: types as any })
    const typesValue = nodes.map((n: any) => [n.parent, n.encoding, n.typeHash])
    // the condition allowSignTypedMessage builds: domain pinned, message
    // free, types pinned (an array of (uint256, uint8, bytes32))
    const S = { paramType: 1, operator: 0 }
    const condition = {
      paramType: 5,
      operator: 5,
      children: [
        {
          paramType: 5,
          operator: 5,
          compValue: "0x0000",
          children: [
            {
              paramType: 1,
              operator: 16,
              compValue: abi.encode(["uint256"], [1]),
            },
            {
              paramType: 1,
              operator: 16,
              compValue: abi.encode(["address"], [libAddr]),
            },
          ],
        },
        {
          paramType: 5,
          operator: 5,
          compValue: "0x0000",
          children: [S, { paramType: 2, operator: 0 }],
        },
        {
          paramType: 4,
          operator: 16,
          compValue: abi.encode(
            ["tuple(uint256,uint8,bytes32)[]"],
            [typesValue]
          ),
          children: [{ paramType: 3, operator: 0, children: [S, S, S] }],
        },
      ],
    }
    const selector = keccak256(
      encodeAbiTypes({ domain, types: types as any })
    ).slice(0, 10)
    await roles.allowFunction(role, libAddr, selector, flat(condition), 2)
    const signTyped = new Interface([
      "function signTypedMessage(bytes domain, bytes message, (uint256 parent, uint8 encoding, bytes32 typeHash)[] types)",
    ])
    const base =
      selector +
      signTyped
        .encodeFunctionData("signTypedMessage", [
          encodeTypedDomain({ domain, types: types as any }),
          encodeTypedMessage({
            types: types as any,
            message: { amount: 5n, note: "hello" },
          } as any),
          typesValue,
        ])
        .slice(10)
    const typesAt = (data: Uint8Array) => {
      const load = (p: number) =>
        BigInt(
          hexlify(Uint8Array.from({ length: 32 }, (_, k) => data[p + k] ?? 0))
        )
      const ptr = Number((load(68) + 4n) % 2n ** 256n)
      const n = Number(load(ptr))
      return { ptr, n, load }
    }
    // the pinned types: those of the unmutated call
    const pinnedTypes = (() => {
      const d = getBytes(base)
      const { ptr, n, load } = typesAt(d)
      return Array.from({ length: n }, (_, i) => [
        load(ptr + 32 + 96 * i),
        load(ptr + 64 + 96 * i),
        toBeHex(load(ptr + 96 + 96 * i), 32),
      ])
    })()
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
      bytesOf(64),
    ]

    const tally = { stored: 0, roles: 0, library: 0, unchecked: 0 }
    for (let i = 0; i < CASES; i++) {
      const data = rnd() < 0.2 ? base : mutate(base, decoys)
      const r = await run(roles, member, libAddr, role, data)
      if (!r.key) {
        count(tally, r.refused!)
        continue
      }
      tally.stored++
      // what the fallback hands to the encoder
      const d = getBytes(data)
      const load = (p: number) =>
        BigInt(
          hexlify(Uint8Array.from({ length: 32 }, (_, k) => d[p + k] ?? 0))
        )
      // The fallback takes `domain` and `message` lengths from the
      // calldata unchecked; past the end it reads zeros. A length far past
      // the end cannot be handed to the reference encoder as bytes.
      const arg = (j: number) => {
        const off = Number((load(4 + 32 * j) + 36n) % 2n ** 256n)
        const len = load(off - 32)
        if (len > BigInt(d.length + 4096)) return undefined
        return hexlify(
          Uint8Array.from({ length: Number(len) }, (_, k) => d[off + k] ?? 0)
        )
      }
      const [a0, a1] = [arg(0), arg(1)]
      if (a0 === undefined || a1 === undefined) {
        tally.unchecked++
        continue
      }
      const digest = await encoder.hashTypedMessage(a0, a1, pinnedTypes)
      expect(r.key, `stored key for ${data}`).to.equal(key(digest))
    }
    console.log("signTypedMessage", tally)
    expect(tally.stored).to.be.greaterThan(0)
  })
})
