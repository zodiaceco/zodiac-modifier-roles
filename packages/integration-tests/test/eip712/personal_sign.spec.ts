import assert from "node:assert/strict"
import { randomBytes } from "node:crypto"
import { after, describe, it } from "node:test"
import {
  type Address,
  type Hex,
  type PublicClient,
  type WalletClient,
  concat,
  encodeAbiParameters,
  encodeFunctionData,
  encodePacked,
  keccak256,
  parseAbi,
  toBytes,
  toHex,
  zeroAddress,
  zeroHash,
} from "viem"
import { network } from "hardhat"

import { safeAbi } from "./setup/safe-deployments/index.js"
import { deploySafe } from "./setup/safe.js"
import deployMastercopies from "./setup/deploy-mastercopies/index.js"

const connection = await network.create()
const { viem, networkHelpers } = connection
const { loadFixture } = networkHelpers

const EIP712_MAGIC_VALUE = "0x1626ba7e"

const SAFE_MSG_TYPEHASH = keccak256(toBytes("SafeMessage(bytes message)"))

const isValidSignatureBytes32Abi = parseAbi([
  "function isValidSignature(bytes32 _dataHash, bytes _signature) view returns (bytes4)",
])
const safeDomainSeparatorAbi = parseAbi([
  "function domainSeparator() view returns (bytes32)",
])
const personalSignAbi = parseAbi(["function personalSign(bytes message)"])

// It's not possible to verify a contract signature (on-chain, "0x") directly
// with viem's standard tooling because it throws on "0x" signatures.
// So we verify with an off-chain EOA 1271 signature via viem's verifyMessage,
// and then compare that the same dataHash is produced by the lib and call
// isValidSignature directly.
describe("personal_sign", () => {
  after(async () => {
    await connection.close()
  })

  async function setup() {
    await deployMastercopies(viem)

    const lib = await viem.deployContract("SignTypedMessageLib")

    const [owner, relayer] = await viem.getWalletClients()
    const publicClient = await viem.getPublicClient()

    const safe = await deploySafe(
      {
        owners: [owner.account.address],
        threshold: 1,
        creationNonce: BigInt(randomHash()),
      },
      owner
    )

    return { owner, relayer, publicClient, safe, lib: lib.address }
  }

  it("isValidSignature with off-chain EOA signature", async () => {
    const { owner, publicClient, safe } = await loadFixture(setup)

    const plainMessage = "hello sir"
    const { dataHash } = await computeSafeMessageHash(
      plainMessage,
      safe,
      publicClient
    )

    // EOA signs the SafeMessage typed data (normal ecrecover, v=27/28)
    const chainId = await publicClient.getChainId()
    const signature = await owner.signTypedData({
      domain: { chainId, verifyingContract: safe },
      types: { SafeMessage: [{ name: "message", type: "bytes" }] },
      primaryType: "SafeMessage",
      message: {
        message: encodeAbiParameters([{ type: "bytes32" }], [dataHash]),
      },
    })

    // viem verifyMessage targeting the Safe (EIP-1271)
    const isValid = await publicClient.verifyMessage({
      address: safe,
      message: plainMessage,
      signature,
    })
    assert.equal(isValid, true)

    // isValidSignature directly via viem
    const result = await publicClient.readContract({
      address: safe,
      abi: isValidSignatureBytes32Abi,
      functionName: "isValidSignature",
      args: [dataHash, signature],
    })
    assert.equal(result, EIP712_MAGIC_VALUE)
  })

  it("isValidSignature with on-chain signMessage", async () => {
    const { owner, publicClient, safe, lib } = await loadFixture(setup)

    const plainMessage = "hello sir"
    const { dataHash } = await computeSafeMessageHash(
      plainMessage,
      safe,
      publicClient
    )

    // Before signing on-chain, isValidSignature with 0x should revert
    await viem.assertions.revert(
      publicClient.readContract({
        address: safe,
        abi: isValidSignatureBytes32Abi,
        functionName: "isValidSignature",
        args: [dataHash, "0x"],
      })
    )

    // Safe calls signMessage("hello sir") via SignTypedMessageLib
    await owner.sendTransaction(
      await encodePersonalSign({ owner, safe, lib, message: plainMessage })
    )

    // Sanity check: direct isValidSignature with 0x works
    const result = await publicClient.readContract({
      address: safe,
      abi: isValidSignatureBytes32Abi,
      functionName: "isValidSignature",
      args: [dataHash, "0x"],
    })
    assert.equal(result, EIP712_MAGIC_VALUE)

    // viem's verifyMessage throws on "0x" signature, so this returns false
    const isValid = await publicClient.verifyMessage({
      address: safe,
      message: plainMessage,
      signature: "0x",
    })
    assert.equal(isValid, false)
  })
})

async function computeSafeMessageHash(
  plainMessage: string,
  safe: Address,
  publicClient: PublicClient
) {
  // EIP-191 personal_sign envelope
  const eip191Envelope = concat([
    toBytes("\x19Ethereum Signed Message:\n"),
    toBytes(String(toBytes(plainMessage).length)),
    toBytes(plainMessage),
  ])
  const dataHash = keccak256(eip191Envelope)

  // isValidSignature(bytes32 _dataHash, ...) internally computes
  // message = abi.encode(_dataHash) before wrapping with Safe's domain
  const message = encodeAbiParameters([{ type: "bytes32" }], [dataHash])

  const domainSeparator = await publicClient.readContract({
    address: safe,
    abi: safeDomainSeparatorAbi,
    functionName: "domainSeparator",
  })

  const safeMessageHash = keccak256(
    encodePacked(
      ["bytes1", "bytes1", "bytes32", "bytes32"],
      [
        "0x19",
        "0x01",
        domainSeparator,
        keccak256(
          encodeAbiParameters(
            [{ type: "bytes32" }, { type: "bytes32" }],
            [SAFE_MSG_TYPEHASH, keccak256(message)]
          )
        ),
      ]
    )
  )

  return { dataHash, safeMessageHash }
}

async function encodePersonalSign({
  owner,
  safe,
  lib,
  message,
}: {
  owner: WalletClient
  safe: Address
  lib: Address
  message: string
}) {
  const data = encodeFunctionData({
    abi: safeAbi,
    functionName: "execTransaction",
    args: [
      lib,
      0n,
      encodeFunctionData({
        abi: personalSignAbi,
        functionName: "personalSign",
        args: [toHex(toBytes(message))],
      }),
      1, // Delegatecall
      0n,
      0n,
      0n,
      zeroAddress,
      zeroAddress,
      createPreApprovedSignature(owner.account!.address),
    ],
  })

  return {
    account: owner.account!,
    chain: owner.chain,
    to: safe,
    data,
    value: 0n,
  }
}

const createPreApprovedSignature = (approver: Address) => {
  return concat([
    encodeAbiParameters([{ type: "address" }], [approver]),
    zeroHash,
    "0x01",
  ])
}

function randomHash(): Hex {
  return toHex(randomBytes(32))
}
