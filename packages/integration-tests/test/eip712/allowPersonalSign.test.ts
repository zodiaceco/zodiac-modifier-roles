import assert from "node:assert/strict"
import { randomBytes } from "node:crypto"
import { after, describe, it } from "node:test"
import {
  type Address,
  type Hex,
  concat,
  encodeAbiParameters,
  hashMessage,
  keccak256,
  parseAbi,
  toBytes,
  toHex,
} from "viem"
import { network } from "hardhat"
import {
  allowPersonalSign,
  encodePersonalSign,
  ExecutionOptions,
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

const EIP712_MAGIC_VALUE = "0x20c13b0b"

const isValidSignatureBytesAbi = parseAbi([
  "function isValidSignature(bytes _data, bytes _signature) view returns (bytes4)",
])
const isValidSignatureBytes32Abi = parseAbi([
  "function isValidSignature(bytes32 _dataHash, bytes _signature) view returns (bytes4)",
])

describe("allowPersonalSign()", () => {
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

    const startsWith = "example.com wants you to sign in"

    const { selector, condition } = allowPersonalSign({ startsWith })

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
      startsWith,
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
    }
  }

  it("allows signing a message that starts with the allowed prefix", async () => {
    const { lib, startsWith, execTransactionFromRoles } =
      await loadFixture(setup)

    const message = startsWith + " with nonce 12345"

    await execTransactionFromRoles({
      to: lib,
      data: encodePersonalSign({ message }) as Hex,
      operation: 1,
    })
  })

  it("allows signing a message that exactly matches the prefix", async () => {
    const { lib, startsWith, execTransactionFromRoles } =
      await loadFixture(setup)

    await execTransactionFromRoles({
      to: lib,
      data: encodePersonalSign({ message: startsWith }) as Hex,
      operation: 1,
    })
  })

  it("rejects signing a message that does not start with the allowed prefix", async () => {
    const { lib, execTransactionFromRoles } = await loadFixture(setup)

    const message = "malicious.com wants you to sign in with nonce 12345"

    await viem.assertions.revertWithCustomError(
      execTransactionFromRoles({
        to: lib,
        data: encodePersonalSign({ message }) as Hex,
        operation: 1,
      }),
      rolesModMastercopy,
      "ConditionViolation"
    )
  })

  it("signs a message through roles and verifies via isValidSignature", async () => {
    const { publicClient, lib, safe, startsWith, execTransactionFromRoles } =
      await loadFixture(setup)

    const message = startsWith + " with session abc"

    // The CompatibilityFallbackHandler bridges isValidSignature(bytes32,bytes)
    // to isValidSignature(bytes,bytes) by passing abi.encode(dataHash) as data.
    // So for the legacy bytes path, we pass abi.encode(keccak256(eip191Preimage))
    const messageBytes = toBytes(message)
    const eip191Preimage = concat([
      toBytes("\x19Ethereum Signed Message:\n"),
      toBytes(String(messageBytes.length)),
      messageBytes,
    ])
    const messageData = encodeAbiParameters(
      [{ type: "bytes32" }],
      [keccak256(eip191Preimage)]
    )

    // Before signing, isValidSignature should revert
    await viem.assertions.revertWith(
      publicClient.readContract({
        address: safe,
        abi: isValidSignatureBytesAbi,
        functionName: "isValidSignature",
        args: [messageData, "0x"],
      }),
      "Hash not approved"
    )

    // Sign the message through roles
    await execTransactionFromRoles({
      to: lib,
      data: encodePersonalSign({ message }) as Hex,
      operation: 1,
    })

    // After signing, isValidSignature should return magic value
    const result = await publicClient.readContract({
      address: safe,
      abi: isValidSignatureBytesAbi,
      functionName: "isValidSignature",
      args: [messageData, "0x"],
    })

    assert.equal(result, EIP712_MAGIC_VALUE)
  })

  it("signs a message and verifies via isValidSignature(bytes32,bytes)", async () => {
    const { publicClient, lib, safe, startsWith, execTransactionFromRoles } =
      await loadFixture(setup)

    const message = startsWith + " with session abc"
    const messageHash = hashMessage(message)

    // Before signing, isValidSignature(bytes32,bytes) should revert
    await viem.assertions.revertWith(
      publicClient.readContract({
        address: safe,
        abi: isValidSignatureBytes32Abi,
        functionName: "isValidSignature",
        args: [messageHash, "0x"],
      }),
      "Hash not approved"
    )

    // Sign the message through roles
    await execTransactionFromRoles({
      to: lib,
      data: encodePersonalSign({ message }) as Hex,
      operation: 1,
    })

    // After signing, isValidSignature(bytes32,bytes) should return magic value
    const result = await publicClient.readContract({
      address: safe,
      abi: isValidSignatureBytes32Abi,
      functionName: "isValidSignature",
      args: [messageHash, "0x"],
    })

    assert.equal(result, "0x1626ba7e")
  })
})

function randomHash(): Hex {
  return toHex(randomBytes(32))
}
