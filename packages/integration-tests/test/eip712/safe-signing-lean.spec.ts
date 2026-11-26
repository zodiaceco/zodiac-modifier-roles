/**
 * Differential test of the signing proofs (packages/evm/formal/SafeSigning)
 * against a real Safe 1.4.1 and its CompatibilityFallbackHandler.
 *
 * For random messages, the Safe delegatecalls SignTypedMessageLib:
 * - the key `personalSign` / `signMessage` store (the `SignMsg` event) is
 *   the key the Lean model computes;
 * - the Lean EIP-191 hash is viem's `hashMessage`, and the handler's
 *   `isValidSignature(hash, "0x")` accepts it after `personalSign`, and
 *   rejects a random other hash;
 * - `signMessage(abi.encode(h))` makes `isValidSignature(h, "0x")` valid
 *   for a random `h`, and `signMessage` of an EIP-191 hash stores the key
 *   of `personalSign` of the text (`signMessage_personal`);
 * - the handler's `getMessageHashForSafe` is the Lean `safeMessageHash`.
 *
 * Skipped without the Lean driver (`cd packages/evm/formal && lake build
 * roles-model`).
 */
import assert from "node:assert/strict"
import { randomBytes } from "node:crypto"
import { spawnSync } from "node:child_process"
import { existsSync } from "node:fs"
import path from "node:path"
import { after, describe, it } from "node:test"
import { fileURLToPath } from "node:url"
import {
  type Address,
  type Hex,
  type PublicClient,
  type WalletClient,
  concat,
  decodeEventLog,
  encodeAbiParameters,
  encodeFunctionData,
  hashMessage,
  parseAbi,
  toHex,
  zeroAddress,
  zeroHash,
} from "viem"
import { network } from "hardhat"

import { safeAbi, safeDeployments } from "./setup/safe-deployments/index.js"
import { deploySafe } from "./setup/safe.js"
import deployMastercopies from "./setup/deploy-mastercopies/index.js"

const here = path.dirname(fileURLToPath(import.meta.url))
const LEAN_BIN = path.resolve(
  here,
  "../../../evm/formal/.lake/build/bin/roles-model"
)
const fallbackHandler =
  safeDeployments["1.4.1"].compatibilityFallbackHandler.address
const CASES = Number(process.env.SAFE_SIGNING_CASES ?? 24)
const MAGIC = "0x1626ba7e"
const SAFE_MSG_TYPEHASH =
  "0x60b3cbf8b4a223d68d641b3b6ddf9a298e7f33710cf3d3a9d1146b5a6150fbca"

const lean = (lines: string[]): string[] => {
  const res = spawnSync(LEAN_BIN, [], {
    input: lines.join("\n") + "\n",
    encoding: "utf8",
    maxBuffer: 1 << 30,
  })
  if (res.status !== 0) throw new Error(res.stderr || "Lean driver failed")
  return res.stdout.trim().split("\n")
}

const connection = await network.create()
const { viem } = connection

const libAbi = parseAbi([
  "function signMessage(bytes message)",
  "function personalSign(bytes message)",
  "event SignMsg(bytes32 indexed msgHash)",
])
const safeDomainSeparatorAbi = parseAbi([
  "function domainSeparator() view returns (bytes32)",
])
const getMessageHashForSafeAbi = parseAbi([
  "function getMessageHashForSafe(address safe, bytes message) view returns (bytes32)",
])
const isValidSignatureBytes32Abi = parseAbi([
  "function isValidSignature(bytes32 _dataHash, bytes _signature) view returns (bytes4)",
])

describe("SignTypedMessageLib and the Safe's handler against Lean", () => {
  after(async () => {
    await connection.close()
  })

  it(`stores the keys the Lean model computes, and the handler accepts exactly the signed hashes (${CASES} messages)`, async (t) => {
    if (!existsSync(LEAN_BIN)) {
      t.skip()
      return
    }
    await deployMastercopies(viem)
    const lib = await viem.deployContract("SignTypedMessageLib")
    const libAddr = lib.address
    const [owner] = await viem.getWalletClients()
    const publicClient = await viem.getPublicClient()
    const safe = await deploySafe(
      {
        owners: [owner.account.address],
        threshold: 1,
        creationNonce: BigInt(toHex(randomBytes(32))),
      },
      owner
    )
    const ds = await publicClient.readContract({
      address: safe,
      abi: safeDomainSeparatorAbi,
      functionName: "domainSeparator",
    })

    // the handler's constant is keccak256("SafeMessage(bytes message)")
    assert.equal(lean(["th"])[0], SAFE_MSG_TYPEHASH)

    const lengths = [0, 1, 9, 10, 11, 99, 100, 101, 1000]
    const messages = Array.from({ length: CASES }, (_, i) =>
      toHex(
        randomBytes(
          i < lengths.length ? lengths[i] : Math.floor(Math.random() * 200)
        )
      )
    )
    const raws = messages.map(() => toHex(randomBytes(32)))

    const queries = messages.flatMap((m, i) => [
      `ph ${m}`,
      `sk personal ${ds} ${m}`,
      `sk msg ${ds} ${raws[i]}`,
      `smh ${SAFE_MSG_TYPEHASH} ${ds} ${m}`,
    ])
    const out = lean(queries)

    const failures: string[] = []
    for (let i = 0; i < messages.length; i++) {
      const m = messages[i]
      const [ph, keyPersonal, keyRaw, smh] = out.slice(4 * i, 4 * i + 4)

      if (ph !== hashMessage({ raw: m }))
        failures.push(
          `EIP-191 hash of ${m}: Lean ${ph}, viem ${hashMessage({ raw: m })}`
        )

      const viaHandler = await publicClient.readContract({
        address: fallbackHandler,
        abi: getMessageHashForSafeAbi,
        functionName: "getMessageHashForSafe",
        args: [safe, m],
      })
      if (viaHandler !== smh)
        failures.push(
          `getMessageHashForSafe(${m}): handler ${viaHandler}, Lean ${smh}`
        )

      // personalSign(m): stored key, and the handler accepts the EIP-191 hash
      const stored = await execLib(
        owner,
        publicClient,
        safe,
        libAddr,
        "personalSign",
        m
      )
      if (stored !== keyPersonal)
        failures.push(
          `personalSign(${m}): stored ${stored}, Lean ${keyPersonal}`
        )
      if (!(await isValid(publicClient, safe, ph as Hex)))
        failures.push(`isValidSignature(${ph}) rejected after personalSign`)
      if (await isValid(publicClient, safe, toHex(randomBytes(32))))
        failures.push(`isValidSignature accepted a random hash`)

      // signMessage(abi.encode(h)): the raw hash h becomes valid
      const h = raws[i]
      const storedRaw = await execLib(
        owner,
        publicClient,
        safe,
        libAddr,
        "signMessage",
        h
      )
      if (storedRaw !== keyRaw)
        failures.push(`signMessage(${h}): stored ${storedRaw}, Lean ${keyRaw}`)
      if (!(await isValid(publicClient, safe, h)))
        failures.push(`isValidSignature(${h}) rejected after signMessage(${h})`)

      // signMessage of an EIP-191 hash stores personalSign's key
      if (i < 4) {
        const again = await execLib(
          owner,
          publicClient,
          safe,
          libAddr,
          "signMessage",
          ph as Hex
        )
        if (again !== keyPersonal)
          failures.push(
            `signMessage(hashMessage(${m})) stored ${again}, personalSign ${keyPersonal}`
          )
      }
    }
    console.log(`      ${CASES} messages`)
    assert.deepEqual(failures.slice(0, 5), [])
  })
})

/** The Safe delegatecalls the library; returns the key of `SignMsg`. */
async function execLib(
  owner: WalletClient,
  publicClient: PublicClient,
  safe: Address,
  lib: Address,
  fn: "personalSign" | "signMessage",
  message: Hex
): Promise<Hex> {
  const hash = await owner.sendTransaction({
    account: owner.account!,
    chain: owner.chain,
    to: safe,
    data: encodeFunctionData({
      abi: safeAbi,
      functionName: "execTransaction",
      args: [
        lib,
        0n,
        encodeFunctionData({
          abi: libAbi,
          functionName: fn,
          args: [message],
        }),
        1, // DelegateCall
        0n,
        0n,
        0n,
        zeroAddress,
        zeroAddress,
        concat([
          encodeAbiParameters([{ type: "address" }], [owner.account!.address]),
          zeroHash,
          "0x01",
        ]),
      ],
    }),
  })
  const rc = await publicClient.waitForTransactionReceipt({ hash })
  for (const l of rc.logs) {
    try {
      const ev = decodeEventLog({
        abi: libAbi,
        data: l.data,
        topics: l.topics,
      })
      if (ev.eventName === "SignMsg") return ev.args.msgHash
    } catch {}
  }
  throw new Error(`${fn}: no SignMsg event (execution failed)`)
}

/** `isValidSignature(bytes32 hash, "0x")` through the Safe's fallback. */
async function isValid(publicClient: PublicClient, safe: Address, hash: Hex) {
  try {
    const res = await publicClient.readContract({
      address: safe,
      abi: isValidSignatureBytes32Abi,
      functionName: "isValidSignature",
      args: [hash, "0x"],
    })
    return res === MAGIC
  } catch {
    return false
  }
}
