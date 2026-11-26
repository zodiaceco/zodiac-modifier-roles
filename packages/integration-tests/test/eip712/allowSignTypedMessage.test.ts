import assert from "node:assert/strict"
import { randomBytes } from "node:crypto"
import { after, describe, it } from "node:test"
import {
  type Address,
  type Hex,
  hashTypedData,
  keccak256,
  parseAbi,
  toHex,
  zeroAddress,
  zeroHash,
} from "viem"
import { network } from "hardhat"
import {
  allowSignTypedMessage,
  encodeSignTypedMessage,
  ExecutionOptions,
  __integration,
} from "zodiac-roles-sdk"

import {
  connectRolesSafeAndMember,
  deployRoles,
  execTransactionWithRole,
  scopeFunction,
  scopeTarget,
} from "./setup/roles.js"
import { deploySafe } from "./setup/safe.js"
import deployMastercopies from "./setup/deploy-mastercopies/index.js"
import { rolesModMastercopy } from "./setup/deploy-mastercopies/rolesMastercopy.js"

const connection = await network.create()
const { viem, networkHelpers } = connection
const { loadFixture } = networkHelpers

const { toAbiTypes } = __integration

const SomeAddress =
  "0x7e2a2fa2a064f693f0a55c5639476d913ff12d05" as `0x${string}`
const AddressOne = "0x0000000000000000000000000000000000000001" as `0x${string}`

const EIP712_MAGIC_VALUE = "0x20c13b0b"

const isValidSignatureBytesAbi = parseAbi([
  "function isValidSignature(bytes _data, bytes _signature) view returns (bytes4)",
])

describe("allowSignTypedMessage()", () => {
  after(async () => {
    await connection.close()
  })

  async function setup() {
    await deployMastercopies(viem)

    const lib = await viem.deployContract("SignTypedMessageLib")

    const [owner, member, relayer] = await viem.getWalletClients()
    const publicClient = await viem.getPublicClient()

    const safe = await deploySafe(
      {
        owners: [owner.account.address],
        threshold: 1,
        creationNonce: BigInt(randomHash()),
      },
      relayer
    )

    const roles = await deployRoles(
      { avatar: safe, target: safe, owner: owner.account.address },
      relayer,
      publicClient
    )

    const { roleKey } = await connectRolesSafeAndMember({
      owner,
      safe,
      roles,
      member: member.account.address,
    })

    await scopeTarget({
      owner,
      roles,
      roleKey,
      target: lib.address,
    })

    const domain = {
      name: "Array Test",
      version: "1",
      chainId: 1,
      verifyingContract:
        "0xCcCCccccCCCCcCCCCCCcCcCccCcCCCcCcccccccC" as `0x${string}`,
    }

    // Define the types for the EIP-712 structured data
    const types = {
      EIP712Domain: [
        { name: "name", type: "string" },
        { name: "version", type: "string" },
        { name: "chainId", type: "uint256" },
        { name: "verifyingContract", type: "address" },
      ],
      Person: [
        { name: "name", type: "string" },
        { name: "wallet", type: "address" },
        { name: "attachments", type: "Attachment[]" },
      ],
      Attachment: [{ name: "filename", type: "string" }],
    } as const

    // The actual data to be signed
    const message = {
      name: "Vitalik",
      wallet: SomeAddress,
      attachments: [
        {
          filename: "document.pdf",
        },
        {
          filename: "image.jpg",
        },
      ],
    }

    const { selector, condition } = allowSignTypedMessage({
      types,
      domain: {
        chainId: 1n,
        verifyingContract: "0xCcCCccccCCCCcCCCCCCcCcCccCcCCCcCcccccccC",
      },
      message: {
        name: "Vitalik",
        wallet: SomeAddress,
      },
    })

    await scopeFunction({
      owner,
      roles,
      roleKey,
      target: lib.address,
      selector: selector as Hex,
      condition,
      executionOptions: ExecutionOptions.Both,
    })

    return {
      relayer,
      publicClient,
      safe,
      roles,
      lib: lib.address,

      execTransactionFromRoles: ({
        to,
        data,
        operation,
      }: {
        to: Address
        data: Hex
        operation: number
      }) =>
        execTransactionWithRole({
          roles,
          roleKey,
          to,
          data,
          operation,
          signer: member,
        }),
      domain,
      message,
      types,
    }
  }

  it("correctly restricts some elements in domain", async () => {
    const { lib, message, domain, types, execTransactionFromRoles } =
      await loadFixture(setup)

    await viem.assertions.revertWithCustomError(
      execTransactionFromRoles({
        to: lib,
        data: encodeSignTypedMessage({
          domain,
          types,
          message: { ...message, name: "Alice" },
        }) as Hex,
        operation: 1,
      }),
      rolesModMastercopy,
      "ConditionViolation"
    )

    await viem.assertions.revertWithCustomError(
      execTransactionFromRoles({
        to: lib,
        data: encodeSignTypedMessage({
          domain: {
            ...domain,
            verifyingContract: zeroAddress,
          },
          types,
          message,
        }) as Hex,
        operation: 1,
      }),
      rolesModMastercopy,
      "ConditionViolation"
    )

    await execTransactionFromRoles({
      to: lib,
      data: encodeSignTypedMessage({ domain, types, message }) as Hex,
      operation: 1,
    })

    // any name for the app
    await execTransactionFromRoles({
      to: lib,
      data: encodeSignTypedMessage({ domain, types, message }) as Hex,
      operation: 1,
    })

    // any version for the app
    await execTransactionFromRoles({
      to: lib,
      data: encodeSignTypedMessage({
        domain: {
          ...domain,
          version: "v3.4.5",
        },
        types,
        message,
      }) as Hex,
      operation: 1,
    })

    await execTransactionFromRoles({
      to: lib,
      data: encodeSignTypedMessage({
        domain: {
          ...domain,
          name: "Our latest super release",
        },
        types,
        message,
      }) as Hex,
      operation: 1,
    })
  })

  it("correctly restricts some elements in message", async () => {
    const { lib, message, domain, types, execTransactionFromRoles } =
      await loadFixture(setup)

    await viem.assertions.revertWithCustomError(
      execTransactionFromRoles({
        to: lib,
        data: encodeSignTypedMessage({
          domain,
          types,
          message: { ...message, name: "Alice" },
        }) as Hex,
        operation: 1,
      }),
      rolesModMastercopy,
      "ConditionViolation"
    )

    await viem.assertions.revertWithCustomError(
      execTransactionFromRoles({
        to: lib,
        data: encodeSignTypedMessage({
          domain,
          types,
          message: { ...message, wallet: AddressOne },
        }) as Hex,
        operation: 1,
      }),
      rolesModMastercopy,
      "ConditionViolation"
    )

    await execTransactionFromRoles({
      to: lib,
      data: encodeSignTypedMessage({
        domain,
        types,
        message: { ...message, attachments: [{ filename: "logs.csv" }] },
      }) as Hex,
      operation: 1,
    })

    // any name for the app
    await execTransactionFromRoles({
      to: lib,
      data: encodeSignTypedMessage({ domain, types, message }) as Hex,
      operation: 1,
    })
  })

  it("correctly enforces exact type layout", async () => {
    const { lib, message, domain, types, execTransactionFromRoles } =
      await loadFixture(setup)

    const data = encodeSignTypedMessage({ domain, types, message }) as Hex
    await execTransactionFromRoles({
      to: lib,
      data: data,
      operation: 1,
    })

    const aTypeHash = toAbiTypes({ domain, types })
      .map((n) => n.typeHash)
      .find((t) => t !== zeroHash)!

    // change one hash
    assert.ok(data.includes(aTypeHash.slice(2)))

    await viem.assertions.revertWithCustomError(
      execTransactionFromRoles({
        to: lib,
        data: data.replace(
          aTypeHash.slice(2),
          keccak256(aTypeHash).slice(2)
        ) as Hex,
        operation: 1,
      }),
      rolesModMastercopy,
      "ConditionViolation"
    )
  })

  it("signs a message from a safe, through a roles mod", async () => {
    const {
      publicClient,
      lib,
      safe,
      message,
      domain,
      types,
      execTransactionFromRoles,
    } = await loadFixture(setup)

    const { EIP712Domain: _, ...messageHashTypes } = types
    const messageHash = hashTypedData({
      domain,
      types: messageHashTypes,
      primaryType: "Person",
      message,
    })

    await viem.assertions.revertWith(
      publicClient.readContract({
        address: safe,
        abi: isValidSignatureBytesAbi,
        functionName: "isValidSignature",
        args: [messageHash, "0x"],
      }),
      "Hash not approved"
    )

    await execTransactionFromRoles({
      to: lib,
      data: encodeSignTypedMessage({ domain, types, message }) as Hex,
      operation: 1,
    })

    const result = await publicClient.readContract({
      address: safe,
      abi: isValidSignatureBytesAbi,
      functionName: "isValidSignature",
      args: [messageHash, "0x"],
    })

    assert.equal(result, EIP712_MAGIC_VALUE)
  })
})

function randomHash(): Hex {
  return toHex(randomBytes(32))
}
