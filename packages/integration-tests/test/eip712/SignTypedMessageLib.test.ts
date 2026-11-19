import { expect } from "chai"
import type { TypedData, TypedDataDomain } from "abitype"
import {
  AbiCoder,
  Interface,
  TypedDataEncoder,
  ZeroAddress,
  ZeroHash,
  concat,
  randomBytes,
} from "ethers"
import type { Signer } from "ethers"
import { network } from "hardhat"
import { encodeSignTypedMessage, __integration } from "zodiac-roles-sdk"

import deployMastercopies from "./setup/deploy-mastercopies/index.js"
import { iface as ifaceFallback } from "./setup/deploy-mastercopies/fallbackHandler.js"
import { iface as ifaceSafe } from "./setup/deploy-mastercopies/safeMastercopy.js"

import { deploySafe } from "./setup/safe.js"

const connection = await network.create()
const { ethers, networkHelpers, provider } = connection
const { loadFixture } = networkHelpers

const EIP712_MAGIC_VALUE = "0x1626ba7e"
const EIP712_MAGIC_VALUE_OLD = "0x20c13b0b"

describe("SignTypedMessageLib", () => {
  after(async () => {
    await connection.close()
  })

  async function setup() {
    await deployMastercopies(ethers)
    const lib = await (
      await ethers.getContractFactory("SignTypedMessageLib")
    ).deploy()

    const [owner, relayer] = await ethers.getSigners()

    const safe = await deploySafe(
      {
        owners: [await owner.getAddress()],
        threshold: 1,
        creationNonce: BigInt(randomHash()),
      },
      owner
    )

    return { owner, relayer, safe, lib: await lib.getAddress() }
  }
  it("signMessage()", async () => {
    const { owner, relayer, safe, lib } = await loadFixture(setup)

    const message = "0xbadfed"

    await owner.sendTransaction(
      await _encodeSignMessage({ owner, safe, lib, message })
    )

    const resultData = await relayer.call({
      to: safe,
      data: ifaceFallback.encodeFunctionData("isValidSignature(bytes,bytes)", [
        message,
        "0x",
      ]),
    })

    const result = ifaceFallback.decodeFunctionResult(
      "isValidSignature(bytes,bytes)",
      resultData
    )

    expect(result).to.deep.equal([EIP712_MAGIC_VALUE_OLD])
  })
  it("signTypedMessage()", async () => {
    const { owner, relayer, safe, lib } = await loadFixture(setup)

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

    const resultData = await relayer.call({
      to: safe,
      data: ifaceFallback.encodeFunctionData("isValidSignature(bytes,bytes)", [
        TypedDataEncoder.hash(domain, types, message),
        "0x",
      ]),
    })

    const result = ifaceFallback.decodeFunctionResult(
      "isValidSignature(bytes,bytes)",
      resultData
    )

    expect(result).to.deep.equal([EIP712_MAGIC_VALUE_OLD])
  })

  it("signTypedMessage() via fallback", async () => {
    const { owner, relayer, safe, lib } = await loadFixture(setup)

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
        "0xABABABababABababABababABababABababABaBab".toLowerCase(),
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

    const hashFromEthers = TypedDataEncoder.hash(domain, types, message)

    const tx = await _encodeSignTypedMessageFallback({
      owner,
      safe,
      lib,
      domain,
      message,
      types,
    })

    await owner.sendTransaction(tx)

    const resultData = await relayer.call({
      to: safe,
      data: ifaceFallback.encodeFunctionData("isValidSignature(bytes,bytes)", [
        hashFromEthers,
        "0x",
      ]),
    })

    const result = ifaceFallback.decodeFunctionResult(
      "isValidSignature(bytes,bytes)",
      resultData
    )

    expect(result).to.deep.equal([EIP712_MAGIC_VALUE_OLD])
  })
  it("fallback - rejects arguments that do not lie within calldata", async () => {
    const { relayer, lib } = await loadFixture(setup)
    const contract = await ethers.getContractAt("SignTypedMessageLib", lib)

    const types = { Message: [{ name: "amount", type: "uint256" }] }
    const encoded = encodeSignTypedMessage({
      domain: { version: "1", chainId: 1 },
      message: { amount: 100 },
      types,
    })
    const data = `0x11223344${encoded.slice(10)}`
    const size = (data.length - 2) / 2

    // the word at byte `position` of data
    const read = (position: number) =>
      Number(BigInt(`0x${data.slice(2 + position * 2, 66 + position * 2)}`))
    // data with the word at byte `position` replaced
    const write = (position: number, value: bigint) =>
      data.slice(0, 2 + position * 2) +
      value.toString(16).padStart(64, "0") +
      data.slice(66 + position * 2)

    const max = 2n ** 256n - 1n
    const [domainLength, messageLength, typesLength] = [
      read(0x04) + 4,
      read(0x24) + 4,
      read(0x44) + 4,
    ]

    // well formed: decoded, and then refused for not being a delegatecall
    await expect(relayer.call({ to: lib, data })).to.be.revertedWithCustomError(
      contract,
      "OnlyDelegateCall"
    )

    const malformed = {
      "selector only": data.slice(0, 10),
      "shorter than the head": data.slice(0, 2 + 0x63 * 2),
      "truncated by one byte": data.slice(0, -2),
      "truncated by one type node": data.slice(0, -0x60 * 2),
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

    for (const [name, data] of Object.entries(malformed)) {
      await expect(
        relayer.call({ to: lib, data }),
        name
      ).to.be.revertedWithCustomError(contract, "InvalidCalldata")
    }
  })
  it("reverts when called directly", async () => {
    const { relayer, lib } = await loadFixture(setup)
    const contract = await ethers.getContractAt("SignTypedMessageLib", lib)

    await expect(
      contract.connect(relayer).signMessage("0xbadfed")
    ).to.be.revertedWithCustomError(contract, "OnlyDelegateCall")
    await expect(
      contract.connect(relayer).personalSign("0xbadfed")
    ).to.be.revertedWithCustomError(contract, "OnlyDelegateCall")
    await expect(
      contract.connect(relayer).signTypedMessage("0x", "0x", [])
    ).to.be.revertedWithCustomError(contract, "OnlyDelegateCall")
  })
})

async function _encodeSignMessage({
  owner,
  safe,
  lib,
  message,
}: {
  owner: Signer
  safe: string
  lib: string
  message: string
}) {
  const iface = Interface.from(["function signMessage(bytes message)"])

  const data = ifaceSafe.encodeFunctionData("execTransaction", [
    lib,
    0,
    iface.encodeFunctionData("signMessage", [message]),
    1, //Delegatecall,
    0n,
    0n,
    0n,
    ZeroAddress,
    ZeroAddress,
    createPreApprovedSignature(await owner.getAddress()),
  ])

  return {
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
  owner: Signer
  safe: string
  lib: string
  domain: TypedDataDomain
  message: Record<string, any>
  types: TypedData
}) {
  const data = ifaceSafe.encodeFunctionData("execTransaction", [
    lib,
    0,
    encodeSignTypedMessage({ domain, message, types }),
    1, //Delegatecall,
    0n,
    0n,
    0n,
    ZeroAddress,
    ZeroAddress,
    createPreApprovedSignature(await owner.getAddress()),
  ])
  return {
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
  owner: Signer
  safe: string
  lib: string
  domain: any
  message: any
  types: any
}) {
  const data = ifaceSafe.encodeFunctionData("execTransaction", [
    lib,
    0,
    `0x11223344${encodeSignTypedMessage({ domain, message, types }).slice(10)}`,
    1, //Delegatecall,
    0n,
    0n,
    0n,
    ZeroAddress,
    ZeroAddress,
    createPreApprovedSignature(await owner.getAddress()),
  ])

  return {
    to: safe,
    data,
    value: 0n,
  }
}

const createPreApprovedSignature = (approver: string) => {
  return concat([
    AbiCoder.defaultAbiCoder().encode(["address"], [approver]),
    ZeroHash,
    "0x01",
  ])
}

function randomHash(): string {
  return (
    "0x" +
    Array.from(randomBytes(32))
      .map((b) => b.toString(16).padStart(2, "0"))
      .join("")
  )
}
