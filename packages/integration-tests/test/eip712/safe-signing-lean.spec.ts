/**
 * Differential test of the signing proofs (packages/evm/formal/SafeSigning)
 * against a real Safe 1.4.1 and its CompatibilityFallbackHandler.
 *
 * For random messages, the Safe delegatecalls SignTypedMessageLib:
 * - the key `personalSign` / `signMessage` store (the `SignMsg` event) is
 *   the key the Lean model computes;
 * - the Lean EIP-191 hash is ethers' `hashMessage`, and the handler's
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
import { expect } from "chai"
import {
  AbiCoder,
  Interface,
  ZeroAddress,
  ZeroHash,
  concat,
  getBytes,
  hashMessage,
  hexlify,
  randomBytes,
} from "ethers"
import type { Signer } from "ethers"
import { network } from "hardhat"
import { spawnSync } from "node:child_process"
import { existsSync } from "node:fs"
import path from "node:path"
import { fileURLToPath } from "node:url"

import {
  address as fallbackHandler,
  iface as ifaceFallback,
} from "./setup/deploy-mastercopies/fallbackHandler.js"
import { iface as ifaceSafe } from "./setup/deploy-mastercopies/safeMastercopy.js"
import { deploySafe } from "./setup/safe.js"
import deployMastercopies from "./setup/deploy-mastercopies/index.js"

const here = path.dirname(fileURLToPath(import.meta.url))
const LEAN_BIN = path.resolve(
  here,
  "../../../evm/formal/.lake/build/bin/roles-model"
)
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
const { ethers } = connection

const libIface = new Interface([
  "function signMessage(bytes message)",
  "function personalSign(bytes message)",
  "event SignMsg(bytes32 indexed msgHash)",
])

describe("SignTypedMessageLib and the Safe's handler against Lean", function () {
  after(async () => {
    await connection.close()
  })

  it(`stores the keys the Lean model computes, and the handler accepts exactly the signed hashes (${CASES} messages)`, async function () {
    if (!existsSync(LEAN_BIN)) this.skip()
    this.timeout(0)
    await deployMastercopies(ethers)
    const lib = await (
      await ethers.getContractFactory("SignTypedMessageLib")
    ).deploy()
    const libAddr = await lib.getAddress()
    const [owner, relayer] = await ethers.getSigners()
    const safe = await deploySafe(
      {
        owners: [await owner.getAddress()],
        threshold: 1,
        creationNonce: BigInt(hexlify(randomBytes(32))),
      },
      owner
    )
    const ds = await relayer.call({
      to: safe,
      data: ifaceSafe.encodeFunctionData("domainSeparator"),
    })

    // the handler's constant is keccak256("SafeMessage(bytes message)")
    expect(lean(["th"])[0]).to.equal(SAFE_MSG_TYPEHASH)

    const lengths = [0, 1, 9, 10, 11, 99, 100, 101, 1000]
    const messages = Array.from({ length: CASES }, (_, i) =>
      hexlify(
        randomBytes(
          i < lengths.length ? lengths[i] : Math.floor(Math.random() * 200)
        )
      )
    )
    const raws = messages.map(() => hexlify(randomBytes(32)))

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

      if (ph !== hashMessage(getBytes(m)))
        failures.push(
          `EIP-191 hash of ${m}: Lean ${ph}, ethers ${hashMessage(getBytes(m))}`
        )

      const viaHandler = ifaceFallback.decodeFunctionResult(
        "getMessageHashForSafe",
        await relayer.call({
          to: fallbackHandler,
          data: ifaceFallback.encodeFunctionData("getMessageHashForSafe", [
            safe,
            m,
          ]),
        })
      )[0]
      if (viaHandler !== smh)
        failures.push(
          `getMessageHashForSafe(${m}): handler ${viaHandler}, Lean ${smh}`
        )

      // personalSign(m): stored key, and the handler accepts the EIP-191 hash
      const stored = await execLib(owner, safe, libAddr, "personalSign", m)
      if (stored !== keyPersonal)
        failures.push(
          `personalSign(${m}): stored ${stored}, Lean ${keyPersonal}`
        )
      if (!(await isValid(relayer, safe, ph)))
        failures.push(`isValidSignature(${ph}) rejected after personalSign`)
      if (await isValid(relayer, safe, hexlify(randomBytes(32))))
        failures.push(`isValidSignature accepted a random hash`)

      // signMessage(abi.encode(h)): the raw hash h becomes valid
      const h = raws[i]
      const storedRaw = await execLib(owner, safe, libAddr, "signMessage", h)
      if (storedRaw !== keyRaw)
        failures.push(`signMessage(${h}): stored ${storedRaw}, Lean ${keyRaw}`)
      if (!(await isValid(relayer, safe, h)))
        failures.push(`isValidSignature(${h}) rejected after signMessage(${h})`)

      // signMessage of an EIP-191 hash stores personalSign's key
      if (i < 4) {
        const again = await execLib(owner, safe, libAddr, "signMessage", ph)
        if (again !== keyPersonal)
          failures.push(
            `signMessage(hashMessage(${m})) stored ${again}, personalSign ${keyPersonal}`
          )
      }
    }
    console.log(`      ${CASES} messages`)
    expect(failures.slice(0, 5)).to.deep.equal([])
  })
})

/** The Safe delegatecalls the library; returns the key of `SignMsg`. */
async function execLib(
  owner: Signer,
  safe: string,
  lib: string,
  fn: "personalSign" | "signMessage",
  message: string
): Promise<string> {
  const tx = await owner.sendTransaction({
    to: safe,
    data: ifaceSafe.encodeFunctionData("execTransaction", [
      lib,
      0,
      libIface.encodeFunctionData(fn, [message]),
      1, // DelegateCall
      0n,
      0n,
      0n,
      ZeroAddress,
      ZeroAddress,
      concat([
        AbiCoder.defaultAbiCoder().encode(
          ["address"],
          [await owner.getAddress()]
        ),
        ZeroHash,
        "0x01",
      ]),
    ]),
  })
  const rc = await tx.wait()
  const ev = rc!.logs
    .map((l) => {
      try {
        return libIface.parseLog(l)
      } catch {
        return null
      }
    })
    .find((e) => e?.name === "SignMsg")
  if (!ev) throw new Error(`${fn}: no SignMsg event (execution failed)`)
  return ev.args.msgHash
}

/** `isValidSignature(bytes32 hash, "0x")` through the Safe's fallback. */
async function isValid(caller: Signer, safe: string, hash: string) {
  try {
    const res = ifaceFallback.decodeFunctionResult(
      "isValidSignature(bytes32,bytes)",
      await caller.call({
        to: safe,
        data: ifaceFallback.encodeFunctionData(
          "isValidSignature(bytes32,bytes)",
          [hash, "0x"]
        ),
      })
    )
    return res[0] === MAGIC
  } catch {
    return false
  }
}
