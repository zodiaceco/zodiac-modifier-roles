/**
 * SignTypedMessageLib against every Safe version it supports, through the
 * entry points used in the wild:
 *
 * - a role member signs an EIP-712 message (a Permit2 permit, given as a
 *   wallet request with `primaryType`) and a Sign-In with Ethereum message,
 *   as text and as the raw bytes of a `personal_sign` request, through the
 *   Roles Modifier;
 * - the owners delegatecall `signMessage(abi.encode(hash))`, Safe's own
 *   SignMessageLib scheme, and `signTypedMessage` under its own selector.
 *
 * Each signature must verify through `isValidSignature(bytes32, "")`, the
 * check dapps make, and store the key the Safe's fallback handler reads.
 * The legacy `isValidSignature(bytes, bytes)` is checked where it exists
 * (1.3.0, 1.4.1), and checked gone where it does not (1.5.0).
 */
import assert from "node:assert/strict"
import { randomBytes } from "node:crypto"
import { after, describe, it } from "node:test"
import {
  type Hex,
  type TransactionReceipt,
  concat,
  decodeEventLog,
  encodeAbiParameters,
  encodeFunctionData,
  hashMessage,
  hashTypedData,
  keccak256,
  parseAbi,
  toFunctionSelector,
  toHex,
  zeroAddress,
  zeroHash,
} from "viem"
import { network } from "hardhat"
import {
  ExecutionOptions,
  allowPersonalSign,
  allowSignTypedMessage,
  encodePersonalSign,
  encodeSignMessage,
  encodeSignTypedMessage,
} from "zodiac-roles-sdk"

import {
  connectRolesSafeAndMember,
  deployRoles,
  execTransactionWithRole,
  scopeFunction,
  scopeTarget,
} from "./setup/roles.js"
import deployMastercopies from "./setup/deploy-mastercopies/index.js"
import {
  type SafeVersion,
  safeAbi,
  safeDeployments,
} from "./setup/safe-deployments/index.js"
import { deploySafe } from "./setup/safe.js"

const versions: {
  version: SafeVersion
  handler: "compatibilityFallbackHandler" | "extensibleFallbackHandler"
  legacyIsValidSignature: boolean
}[] = [
  {
    version: "1.3.0",
    handler: "compatibilityFallbackHandler",
    legacyIsValidSignature: true,
  },
  {
    version: "1.4.1",
    handler: "compatibilityFallbackHandler",
    legacyIsValidSignature: true,
  },
  {
    version: "1.5.0",
    handler: "compatibilityFallbackHandler",
    legacyIsValidSignature: false,
  },
  {
    version: "1.5.0",
    handler: "extensibleFallbackHandler",
    legacyIsValidSignature: false,
  },
]

const MAGIC = "0x1626ba7e"
const LEGACY_MAGIC = "0x20c13b0b"
const SAFE_MSG_TYPEHASH = keccak256(toHex("SafeMessage(bytes message)"))

const PERMIT2 = "0x000000000022D473030F116dDEE9F6B43aC78BA3" as const
const TOKEN = "0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48" as const
const SPENDER = "0x66a9893cC07D91D95644AEDD05D03f95e1dBA8Af" as const

// a Permit2 permit as dapps request it (`eth_signTypedData_v4`)
const permitTypes = {
  EIP712Domain: [
    { name: "name", type: "string" },
    { name: "chainId", type: "uint256" },
    { name: "verifyingContract", type: "address" },
  ],
  PermitDetails: [
    { name: "token", type: "address" },
    { name: "amount", type: "uint160" },
    { name: "expiration", type: "uint48" },
    { name: "nonce", type: "uint48" },
  ],
  PermitSingle: [
    { name: "details", type: "PermitDetails" },
    { name: "spender", type: "address" },
    { name: "sigDeadline", type: "uint256" },
  ],
  PermitBatch: [
    { name: "details", type: "PermitDetails[]" },
    { name: "spender", type: "address" },
    { name: "sigDeadline", type: "uint256" },
  ],
} as const

const SIWE_PREFIX =
  "app.example wants you to sign in with your Ethereum account:\n"

const libAbi = parseAbi(["event SignMsg(bytes32 indexed msgHash)"])
const isValidSignatureAbi = parseAbi([
  "function isValidSignature(bytes32 _dataHash, bytes _signature) view returns (bytes4)",
])
const legacyAbi = parseAbi([
  "function isValidSignature(bytes _data, bytes _signature) view returns (bytes4)",
])

const connection = await network.create()
const { viem, networkHelpers } = connection

after(async () => {
  await connection.close()
})

for (const version of versions) {
  const handlerName =
    version.handler === "compatibilityFallbackHandler"
      ? "CompatibilityFallbackHandler"
      : "ExtensibleFallbackHandler"

  describe(`SignTypedMessageLib on Safe ${version.version}, ${handlerName}`, () => {
    async function setup() {
      await deployMastercopies(viem)
      const lib = (await viem.deployContract("SignTypedMessageLib")).address

      const [owner, member, relayer] = await viem.getWalletClients()
      const publicClient = await viem.getPublicClient()

      const safe = await deploySafe(
        {
          owners: [owner.account.address],
          threshold: 1,
          creationNonce: BigInt(toHex(randomBytes(32))),
          version: version.version,
          fallbackHandler:
            safeDeployments[version.version][version.handler]!.address,
        },
        relayer
      )
      assert.ok(await publicClient.getCode({ address: safe }))

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
      await scopeTarget({ owner, roles, roleKey, target: lib })

      const chainId = await publicClient.getChainId()
      for (const { selector, condition } of [
        allowSignTypedMessage({
          types: permitTypes,
          primaryType: "PermitSingle",
          domain: { chainId: BigInt(chainId), verifyingContract: PERMIT2 },
          message: { details: { token: TOKEN }, spender: SPENDER },
        }),
        allowPersonalSign({ startsWith: SIWE_PREFIX }),
      ]) {
        await scopeFunction({
          owner,
          roles,
          roleKey,
          target: lib,
          selector,
          condition,
          executionOptions: ExecutionOptions.DelegateCall,
        })
      }

      const domainSeparator = await publicClient.readContract({
        address: safe,
        abi: safeAbi,
        functionName: "domainSeparator",
      })

      /** The member delegatecalls the library through the Roles Modifier. */
      const asMember = async (data: Hex) =>
        publicClient.waitForTransactionReceipt({
          hash: await execTransactionWithRole({
            signer: member,
            roles,
            roleKey,
            to: lib,
            data,
            operation: 1,
          }),
        })

      /** The owners delegatecall the library with a Safe transaction. */
      const asOwners = async (data: Hex) =>
        publicClient.waitForTransactionReceipt({
          hash: await owner.sendTransaction({
            account: owner.account,
            chain: owner.chain,
            to: safe,
            data: encodeFunctionData({
              abi: safeAbi,
              functionName: "execTransaction",
              args: [
                lib,
                0n,
                data,
                1,
                0n,
                0n,
                0n,
                zeroAddress,
                zeroAddress,
                concat([
                  encodeAbiParameters(
                    [{ type: "address" }],
                    [owner.account.address]
                  ),
                  zeroHash,
                  "0x01",
                ]),
              ],
            }),
          }),
        })

      /** `isValidSignature(hash, "0x")` accepts `hash`. */
      const isValid = async (hash: Hex) =>
        (await call(() =>
          publicClient.readContract({
            address: safe,
            abi: isValidSignatureAbi,
            functionName: "isValidSignature",
            args: [hash, "0x"],
          })
        )) === MAGIC

      /** The key the handler reads for `isValidSignature(bytes)`. */
      const keyOf = (message: Hex) =>
        keccak256(
          concat([
            "0x1901",
            domainSeparator,
            keccak256(
              encodeAbiParameters(
                [{ type: "bytes32" }, { type: "bytes32" }],
                [SAFE_MSG_TYPEHASH, keccak256(message)]
              )
            ),
          ])
        )

      return {
        safe,
        chainId,
        publicClient,
        asMember,
        asOwners,
        isValid,
        keyOf,
      }
    }

    const permit = (chainId: number, amount = 1_000_000n) => ({
      domain: {
        name: "Permit2",
        chainId: BigInt(chainId),
        verifyingContract: PERMIT2,
      },
      types: permitTypes,
      primaryType: "PermitSingle" as const,
      message: {
        details: { token: TOKEN, amount, expiration: 1_900_000_000, nonce: 0 },
        spender: SPENDER,
        sigDeadline: 1_900_000_000n,
      },
    })

    it("a member signs a Permit2 permit through the Roles Modifier", async () => {
      const { chainId, asMember, isValid, keyOf } =
        await networkHelpers.loadFixture(setup)

      const typedData = permit(chainId)
      const hash = hashTypedData(typedData)
      assert.equal(await isValid(hash), false)

      const receipt = await asMember(encodeSignTypedMessage(typedData))

      assert.equal(signedKey(receipt), keyOf(hash))
      assert.equal(await isValid(hash), true)
      // the approval is of this permit only
      assert.equal(
        await isValid(hashTypedData(permit(chainId, 1_000_001n))),
        false
      )
    })

    it("a member signs in with Ethereum, as text and as raw bytes", async () => {
      const { asMember, isValid, keyOf } =
        await networkHelpers.loadFixture(setup)

      const text = `${SIWE_PREFIX}0x${"ab".repeat(20)}\n\nNonce: ${toHex(randomBytes(8))}`
      const asText = await asMember(encodePersonalSign({ message: text }))
      assert.equal(signedKey(asText), keyOf(hashMessage(text)))
      assert.equal(await isValid(hashMessage(text)), true)

      // the hex parameter of a `personal_sign` request
      const raw = toHex(`${SIWE_PREFIX}${toHex(randomBytes(8))}`)
      const asRaw = await asMember(encodePersonalSign({ message: { raw } }))
      assert.equal(signedKey(asRaw), keyOf(hashMessage({ raw })))
      assert.equal(await isValid(hashMessage({ raw })), true)
    })

    it("the owners sign a hash with signMessage, as Safe's SignMessageLib does", async () => {
      const { asOwners, isValid, keyOf } =
        await networkHelpers.loadFixture(setup)

      const hash = toHex(randomBytes(32))
      const receipt = await asOwners(encodeSignMessage({ message: hash }))

      assert.equal(signedKey(receipt), keyOf(hash))
      assert.equal(await isValid(hash), true)
    })

    it("the owners sign typed data under signTypedMessage's own selector", async () => {
      const { chainId, asOwners, isValid, keyOf } =
        await networkHelpers.loadFixture(setup)

      const typedData = permit(chainId, 42n)
      const hash = hashTypedData(typedData)
      const data = concat([
        toFunctionSelector(
          "signTypedMessage(bytes,bytes,(uint256,uint8,bytes32)[])"
        ),
        `0x${encodeSignTypedMessage(typedData).slice(10)}`,
      ])

      const receipt = await asOwners(data)

      assert.equal(signedKey(receipt), keyOf(hash))
      assert.equal(await isValid(hash), true)
    })

    it(
      version.legacyIsValidSignature
        ? "the legacy isValidSignature(bytes, bytes) accepts a signed message of any length"
        : "the legacy isValidSignature(bytes, bytes) is gone",
      async () => {
        const { safe, publicClient, asOwners } =
          await networkHelpers.loadFixture(setup)

        const message = toHex(randomBytes(45))
        await asOwners(encodeSignMessage({ message }))

        const result = await call(() =>
          publicClient.readContract({
            address: safe,
            abi: legacyAbi,
            functionName: "isValidSignature",
            args: [message, "0x"],
          })
        )
        assert.equal(
          result,
          version.legacyIsValidSignature ? LEGACY_MAGIC : undefined
        )
      }
    )
  })
}

/** The key of the `SignMsg` the Safe emitted, i.e. what it stored. */
function signedKey(receipt: TransactionReceipt): Hex {
  for (const log of receipt.logs) {
    try {
      const event = decodeEventLog({
        abi: libAbi,
        data: log.data,
        topics: log.topics,
      })
      return event.args.msgHash
    } catch {}
  }
  throw new Error("no SignMsg event")
}

/** The result of a view call, or undefined if it reverts. */
async function call<T>(read: () => Promise<T>): Promise<T | undefined> {
  try {
    return await read()
  } catch {
    return undefined
  }
}
