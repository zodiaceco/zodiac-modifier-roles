import assert from "node:assert/strict"
import { randomBytes } from "node:crypto"
import { after, describe, it } from "node:test"
import type { TypedData, TypedDataDomain } from "abitype"
import {
  type Address,
  type Hex,
  type WalletClient,
  concat,
  encodeAbiParameters,
  encodeFunctionData,
  hashTypedData,
  parseAbi,
  toHex,
  zeroAddress,
  zeroHash,
} from "viem"
import { network } from "hardhat"
import { encodeSignTypedMessage } from "zodiac-roles-sdk"

import deployMastercopies from "./setup/deploy-mastercopies/index.js"
import { safeAbi } from "./setup/safe-deployments/index.js"

import { deploySafe } from "./setup/safe.js"

const connection = await network.create()
const { viem, networkHelpers } = connection
const { loadFixture } = networkHelpers

const EIP712_MAGIC_VALUE = "0x1626ba7e"
const EIP712_MAGIC_VALUE_OLD = "0x20c13b0b"

const isValidSignatureBytesAbi = parseAbi([
  "function isValidSignature(bytes _data, bytes _signature) view returns (bytes4)",
])
const signMessageAbi = parseAbi(["function signMessage(bytes message)"])

describe("SignTypedMessageLib", () => {
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
  it("signMessage()", async () => {
    const { owner, publicClient, safe, lib } = await loadFixture(setup)

    const message = "0xbadfed"

    await owner.sendTransaction(
      await _encodeSignMessage({ owner, safe, lib, message })
    )

    const result = await publicClient.readContract({
      address: safe,
      abi: isValidSignatureBytesAbi,
      functionName: "isValidSignature",
      args: [message, "0x"],
    })

    assert.equal(result, EIP712_MAGIC_VALUE_OLD)
  })
  it("signTypedMessage()", async () => {
    const { owner, publicClient, safe, lib } = await loadFixture(setup)

    const domain = {
      version: "1",
      chainId: 1, // Mainnet
    }

    const types = {
      Message: [
        { name: "amount", type: "uint256" },
        { name: "message", type: "string" },
      ],
    }

    const message = {
      amount: 100,
      message: "Hello World",
    }

    await owner.sendTransaction(
      await _encodeSignTypedMessage({
        owner,
        safe,
        lib,
        domain,
        message,
        types,
      })
    )

    const result = await publicClient.readContract({
      address: safe,
      abi: isValidSignatureBytesAbi,
      functionName: "isValidSignature",
      args: [
        hashTypedData({
          domain,
          types,
          primaryType: "Message",
          message,
        }),
        "0x",
      ],
    })

    assert.equal(result, EIP712_MAGIC_VALUE_OLD)
  })

  it("signTypedMessage() via fallback", async () => {
    const { owner, publicClient, safe, lib } = await loadFixture(setup)

    const types = {
      Order: [
        { name: "maker", type: "Person" },
        { name: "taker", type: "Person" },
        { name: "asset", type: "Asset" },
        { name: "price", type: "uint256" },
        { name: "expiry", type: "uint256" },
      ],
      Person: [
        { name: "wallet", type: "address" },
        { name: "reputation", type: "uint256" },
      ],
      Asset: [
        { name: "tokenAddress", type: "address" },
        { name: "tokenId", type: "uint256" },
        { name: "amount", type: "uint256" },
      ],
    }

    const domain = {
      name: "TradePlatform",
      version: "1.0",
      chainId: 137,
      verifyingContract:
        "0xABABABababABababABababABababABababABaBab".toLowerCase() as Address,
    }
    const message = {
      maker: {
        wallet: "0x1111111111111111111111111111111111111111",
        reputation: 100,
      },
      taker: {
        wallet: "0x2222222222222222222222222222222222222222",
        reputation: 200,
      },
      asset: {
        tokenAddress: "0x3333333333333333333333333333333333333333",
        tokenId: 12345,
        amount: 1,
      },
      price: 5000000000000,
      expiry: 1710000000,
    }

    const hashFromViem = hashTypedData({
      domain,
      types,
      primaryType: "Order",
      message,
    })

    const tx = await _encodeSignTypedMessageFallback({
      owner,
      safe,
      lib,
      domain,
      message,
      types,
    })

    await owner.sendTransaction(tx)

    const result = await publicClient.readContract({
      address: safe,
      abi: isValidSignatureBytesAbi,
      functionName: "isValidSignature",
      args: [hashFromViem, "0x"],
    })

    assert.equal(result, EIP712_MAGIC_VALUE_OLD)
  })
  it("fallback - rejects arguments that do not lie within calldata", async () => {
    const { relayer, lib } = await loadFixture(setup)
    const contract = await viem.getContractAt("SignTypedMessageLib", lib)

    const types = { Message: [{ name: "amount", type: "uint256" }] } as const
    const encoded = encodeSignTypedMessage({
      domain: { version: "1", chainId: 1 },
      message: { amount: 100n },
      types,
    })
    const data = `0x11223344${encoded.slice(10)}` as Hex
    const size = (data.length - 2) / 2

    // the word at byte `position` of data
    const read = (position: number) =>
      Number(BigInt(`0x${data.slice(2 + position * 2, 66 + position * 2)}`))
    // data with the word at byte `position` replaced
    const write = (position: number, value: bigint): Hex =>
      (data.slice(0, 2 + position * 2) +
        value.toString(16).padStart(64, "0") +
        data.slice(66 + position * 2)) as Hex

    const max = 2n ** 256n - 1n
    const [domainLength, messageLength, typesLength] = [
      read(0x04) + 4,
      read(0x24) + 4,
      read(0x44) + 4,
    ]

    // well formed: decoded, and then refused for not being a delegatecall
    await viem.assertions.revertWithCustomError(
      relayer.sendTransaction({ to: lib, data }),
      contract,
      "OnlyDelegateCall"
    )

    const malformed = {
      "selector only": data.slice(0, 10) as Hex,
      "shorter than the head": data.slice(0, 2 + 0x63 * 2) as Hex,
      "truncated by one byte": data.slice(0, -2) as Hex,
      "truncated by one type node": data.slice(0, -0x60 * 2) as Hex,
      "domain offset wraps": write(0x04, max - 3n),
      "message offset wraps": write(0x24, max - 3n),
      "types offset wraps": write(0x44, max - 3n),
      "domain offset wraps to its own content": write(0x04, max - 0x23n),
      "domain offset at the end": write(0x04, BigInt(size - 4)),
      "types offset past the end": write(0x44, BigInt(size)),
      "domain length past the end": write(
        domainLength,
        BigInt(size - domainLength - 0x20 + 1)
      ),
      "domain length wraps": write(domainLength, max),
      "message length past the end": write(
        messageLength,
        BigInt(size - messageLength - 0x20 + 1)
      ),
      "types length past the end": write(
        typesLength,
        BigInt(read(typesLength) + 1)
      ),
      "types length wraps": write(typesLength, max / 0x60n + 2n),
    }

    for (const [name, malformedData] of Object.entries(malformed)) {
      try {
        await viem.assertions.revertWithCustomError(
          relayer.sendTransaction({ to: lib, data: malformedData }),
          contract,
          "InvalidCalldata"
        )
      } catch (error) {
        throw new Error(
          `${name}: ${error instanceof Error ? error.message : String(error)}`
        )
      }
    }
  })
  it("reverts when called directly", async () => {
    const { relayer, lib } = await loadFixture(setup)
    const contract = await viem.getContractAt("SignTypedMessageLib", lib)

    await viem.assertions.revertWithCustomError(
      contract.write.signMessage(["0xbadfed"], { account: relayer.account }),
      contract,
      "OnlyDelegateCall"
    )
    await viem.assertions.revertWithCustomError(
      contract.write.personalSign(["0xbadfed"], { account: relayer.account }),
      contract,
      "OnlyDelegateCall"
    )
    await viem.assertions.revertWithCustomError(
      contract.write.signTypedMessage(["0x", "0x", []], {
        account: relayer.account,
      }),
      contract,
      "OnlyDelegateCall"
    )
  })
})

async function _encodeSignMessage({
  owner,
  safe,
  lib,
  message,
}: {
  owner: WalletClient
  safe: Address
  lib: Address
  message: Hex
}) {
  const data = encodeFunctionData({
    abi: safeAbi,
    functionName: "execTransaction",
    args: [
      lib,
      0n,
      encodeFunctionData({
        abi: signMessageAbi,
        functionName: "signMessage",
        args: [message],
      }),
      1, //Delegatecall,
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

async function _encodeSignTypedMessage({
  owner,
  safe,
  lib,
  domain,
  message,
  types,
}: {
  owner: WalletClient
  safe: Address
  lib: Address
  domain: TypedDataDomain
  message: Record<string, any>
  types: TypedData
}) {
  const data = encodeFunctionData({
    abi: safeAbi,
    functionName: "execTransaction",
    args: [
      lib,
      0n,
      encodeSignTypedMessage({ domain, message, types }) as Hex,
      1, //Delegatecall,
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

async function _encodeSignTypedMessageFallback({
  owner,
  safe,
  lib,
  domain,
  message,
  types,
}: {
  owner: WalletClient
  safe: Address
  lib: Address
  domain: any
  message: any
  types: any
}) {
  const data = encodeFunctionData({
    abi: safeAbi,
    functionName: "execTransaction",
    args: [
      lib,
      0n,
      `0x11223344${encodeSignTypedMessage({ domain, message, types }).slice(10)}` as Hex,
      1, //Delegatecall,
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
