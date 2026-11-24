/**
 * End-to-end composition of Roles v3 with real Safes (1.4.1, with the
 * CompatibilityFallbackHandler), SignTypedMessageLib and MultiSend.
 *
 * Each case shows how authority or state flows across contracts, not what one
 * function does on its own. They pin down documented behaviour:
 * - a signature of a Safe counts wherever its EIP-1271 signature does, so a
 *   role that can make it sign raw hashes acts with that Safe's roles
 *   (docs: general/signing, "What a signature authorizes"); its digest is
 *   still used once, and only until its deadline;
 * - authorization runs before execution, against the allowance as it is
 *   then; settlement runs after: for allowances it re-accrues from current
 *   storage and deducts consumption (reverting if an executed call reduced
 *   the allowance below what was consumed); for memberships it reads the
 *   membership as the executed transaction left it, so a revocation by the
 *   batch stands (docs: general/allowances and general/membership).
 */
import assert from "node:assert/strict"
import { after, before, describe, it } from "node:test"
import { network } from "hardhat"
import {
  encodeFunctionData,
  hashTypedData,
  parseAbi,
  parseEther,
  toFunctionSelector,
} from "viem"
import type { Address, Hex } from "viem"
import { generatePrivateKey, privateKeyToAccount } from "viem/accounts"

import deployMastercopies from "../eip712/setup/deploy-mastercopies/index.js"
import {
  Encoding,
  ExecutionOptions,
  NO_DEADLINE,
  Operator,
  ROLE_TX_TYPES,
  deployMultiSend,
  encodeMultiSend,
  randomKey,
  safeWithRoles,
} from "./helpers.js"
import type { RoleTx } from "./helpers.js"
import { assertNotEmitted } from "../../../evm/test/utils.js"

const connection = await network.create()
const { viem } = connection

const libAbi = parseAbi(["function signMessage(bytes message)"])

describe("Roles composition, end to end", () => {
  before(async () => {
    await deployMastercopies(viem)
  })
  after(async () => {
    await connection.close()
  })

  it("a role that can make a member Safe sign raw hashes acts with that Safe's roles (ERC-1271)", async () => {
    const [ownerA, ownerM, signerS, relayer] = await viem.getWalletClients()
    const publicClient = await viem.getPublicClient()
    const lib = await viem.deployContract("SignTypedMessageLib")

    // Safe A with Roles R. Safe M is a module of R with role B: send 1 ETH to Y.
    const { safe: safeA, roles: R } = await safeWithRoles(viem, ownerA)
    const { safe: safeM, roles: Rm } = await safeWithRoles(viem, ownerM)
    await ownerA.sendTransaction({ to: safeA, value: parseEther("2") })
    const Y = privateKeyToAccount(generatePrivateKey()).address
    const roleB = randomKey()
    await R.write.grantRole([safeM, roleB, 0n, 0n, 0n], {
      account: ownerA.account,
    })
    await R.write.scopeTarget([roleB, Y], { account: ownerA.account })
    await R.write.allowTarget([roleB, Y, [], ExecutionOptions.Send], {
      account: ownerA.account,
    })

    // Safe M's own Roles Rm: role S may only make M sign messages.
    const roleS = randomKey()
    await Rm.write.grantRole([signerS.account.address, roleS, 0n, 0n, 0n], {
      account: ownerM.account,
    })
    await Rm.write.scopeTarget([roleS, lib.address], {
      account: ownerM.account,
    })
    await Rm.write.allowFunction(
      [
        roleS,
        lib.address,
        toFunctionSelector("signMessage(bytes)"),
        [],
        ExecutionOptions.DelegateCall,
      ],
      { account: ownerM.account }
    )

    const chainId = await publicClient.getChainId()

    /** S makes M sign the digest of a RoleTx for R, role B: 1 ETH to Y. */
    const signedByM = async (deadline: bigint): Promise<RoleTx> => {
      const message: RoleTx = {
        to: Y,
        value: parseEther("1"),
        data: "0x",
        operation: 0,
        roleKey: roleB,
        salt: randomKey(),
        deadline,
      }
      const digest = hashTypedData({
        domain: {
          chainId,
          verifyingContract: R.address,
        },
        types: ROLE_TX_TYPES,
        primaryType: "RoleTx",
        message,
      })
      await Rm.write.execTransactionWithRole(
        [
          lib.address,
          0n,
          encodeFunctionData({
            abi: libAbi,
            functionName: "signMessage",
            args: [digest],
          }),
          1,
          roleS,
        ],
        { account: signerS.account }
      )
      return message
    }

    // Anyone relays it with M's contract signature (address, empty payload).
    const message = await signedByM(NO_DEADLINE)
    await R.write.execTransactionWithRoleSigned([message, safeM], {
      account: relayer.account,
    })
    assert.equal(await publicClient.getBalance({ address: Y }), parseEther("1"))

    // M's approval of the digest stays, but the digest is used once.
    await viem.assertions.revertWithCustomError(
      R.write.execTransactionWithRoleSigned([message, safeM], {
        account: relayer.account,
      }),
      R,
      "HashAlreadyConsumed"
    )

    // An approved digest past its deadline moves nothing.
    const expired = await signedByM((await publicClient.getBlock()).timestamp)
    await viem.assertions.revertWithCustomError(
      R.write.execTransactionWithRoleSigned([expired, safeM], {
        account: relayer.account,
      }),
      R,
      "SignatureExpired"
    )
    assert.equal(await publicClient.getBalance({ address: Y }), parseEther("1"))
  })

  describe("settlement re-accrues allowances from storage after the executed batch", () => {
    /** Role P sends ether to Y within allowance K, and may call
     *  R.setAllowance; the Safe owns R. */
    async function setup() {
      const [ownerA, member] = await viem.getWalletClients()
      const publicClient = await viem.getPublicClient()
      const { safe: safeA, roles: R } = await safeWithRoles(viem, ownerA)
      const Raddr = R.address
      await ownerA.sendTransaction({ to: safeA, value: parseEther("1") })

      const multiSendAddr = await deployMultiSend(viem, R, ownerA)

      const K = randomKey()
      const roleP = randomKey()
      const Y = privateKeyToAccount(generatePrivateKey()).address
      await R.write.grantRole([member.account.address, roleP, 0n, 0n, 0n], {
        account: ownerA.account,
      })
      await R.write.setDefaultRole([member.account.address, roleP], {
        account: ownerA.account,
      })
      await R.write.scopeTarget([roleP, Y], { account: ownerA.account })
      await R.write.allowTarget(
        [
          roleP,
          Y,
          [
            {
              parent: 0,
              paramType: Encoding.EtherValue,
              operator: Operator.WithinAllowance,
              compValue: K,
            },
          ],
          ExecutionOptions.Send,
        ],
        { account: ownerA.account }
      )
      await R.write.scopeTarget([roleP, Raddr], { account: ownerA.account })
      await R.write.allowFunction(
        [
          roleP,
          Raddr,
          toFunctionSelector(
            "setAllowance(bytes32,uint128,uint128,uint128,uint64,uint64)"
          ),
          [],
          ExecutionOptions.None,
        ],
        { account: ownerA.account }
      )

      /** A batch setting K to `balance`, then sending 10 to Y. */
      const setThenSend = (balance: bigint | number) =>
        encodeMultiSend([
          {
            to: Raddr,
            value: 0n,
            data: encodeFunctionData({
              abi: R.abi,
              functionName: "setAllowance",
              args: [K, BigInt(balance), 0n, 0n, 0n, 0n],
            }),
            operation: 0,
          },
          { to: Y, value: 10n, data: "0x", operation: 0 },
        ])

      return {
        ownerA,
        member,
        publicClient,
        safeA,
        R,
        multiSendAddr,
        K,
        roleP,
        Y,
        setThenSend,
      }
    }

    it("reverts when the batch lowered the allowance below its consumption, on either entrypoint", async () => {
      const {
        ownerA,
        member,
        publicClient,
        safeA,
        R,
        multiSendAddr,
        K,
        roleP,
        Y,
        setThenSend,
      } = await setup()
      await R.write.setAllowance([K, 100n, 0n, 0n, 0n, 0n], {
        account: ownerA.account,
      })
      await R.write.transferOwnership([safeA], { account: ownerA.account })

      await viem.assertions.revertWithCustomErrorWithArgs(
        R.write.execTransactionWithRole(
          [multiSendAddr, 0n, setThenSend(0), 1, roleP],
          { account: member.account }
        ),
        R,
        "AllowanceExceeded",
        [K]
      )
      // settlement reverts: no `false` from the IAvatar entrypoint either
      await viem.assertions.revertWithCustomErrorWithArgs(
        R.write.execTransactionFromModule(
          [multiSendAddr, 0n, setThenSend(0), 1],
          { account: member.account }
        ),
        R,
        "AllowanceExceeded",
        [K]
      )
      assert.equal(await publicClient.getBalance({ address: Y }), 0n)
      assert.equal((await R.read.allowances([K]))[3], 100n)
    })

    it("deducts from the balance the batch set, not the one before it", async () => {
      const {
        ownerA,
        member,
        publicClient,
        safeA,
        R,
        multiSendAddr,
        K,
        roleP,
        Y,
        setThenSend,
      } = await setup()
      await R.write.setAllowance([K, 100n, 0n, 0n, 0n, 0n], {
        account: ownerA.account,
      })
      await R.write.transferOwnership([safeA], { account: ownerA.account })

      // 50 - 10, not 100 - 10
      await R.write.execTransactionWithRole(
        [multiSendAddr, 0n, setThenSend(50), 1, roleP],
        { account: member.account }
      )
      assert.equal(await publicClient.getBalance({ address: Y }), 10n)
      assert.equal((await R.read.allowances([K]))[3], 40n)
    })

    it("authorizes against the balance before execution, which a raise in the batch cannot help", async () => {
      const {
        ownerA,
        member,
        publicClient,
        safeA,
        R,
        multiSendAddr,
        K,
        roleP,
        Y,
        setThenSend,
      } = await setup()
      await R.write.setAllowance([K, 5n, 0n, 0n, 0n, 0n], {
        account: ownerA.account,
      })
      await R.write.transferOwnership([safeA], { account: ownerA.account })

      await viem.assertions.revertWithCustomError(
        R.write.execTransactionWithRole(
          [multiSendAddr, 0n, setThenSend(100), 1, roleP],
          { account: member.account }
        ),
        R,
        "ConditionViolation"
      )
      assert.equal(await publicClient.getBalance({ address: Y }), 0n)
      assert.equal((await R.read.allowances([K]))[3], 5n)
    })
  })

  describe("settlement does not restore a limited membership the executed batch revoked", () => {
    /** Role P (5 uses) sends ether to Y and may call R.revokeRole; the Safe
     *  owns R. */
    async function setup() {
      const [ownerA, member] = await viem.getWalletClients()
      const publicClient = await viem.getPublicClient()
      const { safe: safeA, roles: R } = await safeWithRoles(viem, ownerA)
      const Raddr = R.address
      await ownerA.sendTransaction({ to: safeA, value: parseEther("1") })

      const multiSendAddr = await deployMultiSend(viem, R, ownerA)
      const reverter = (await viem.deployContract("Reverter")).address

      const roleP = randomKey()
      const memberAddr = member.account.address
      const Y = privateKeyToAccount(generatePrivateKey()).address
      await R.write.grantRole([memberAddr, roleP, 0n, 0n, 5n], {
        account: ownerA.account,
      })
      for (const t of [Y, reverter]) {
        await R.write.scopeTarget([roleP, t], { account: ownerA.account })
        await R.write.allowTarget([roleP, t, [], ExecutionOptions.Send], {
          account: ownerA.account,
        })
      }
      await R.write.scopeTarget([roleP, Raddr], { account: ownerA.account })
      await R.write.allowFunction(
        [
          roleP,
          Raddr,
          toFunctionSelector("revokeRole(address,bytes32)"),
          [],
          ExecutionOptions.None,
        ],
        { account: ownerA.account }
      )
      await R.write.transferOwnership([safeA], { account: ownerA.account })

      /** A batch sending 10 to Y and revoking the member's role, then
       *  calling `last` if given. */
      const sendRevoke = (last?: Address) =>
        encodeMultiSend([
          { to: Y, value: 10n, data: "0x", operation: 0 },
          {
            to: Raddr,
            value: 0n,
            data: encodeFunctionData({
              abi: R.abi,
              functionName: "revokeRole",
              args: [memberAddr, roleP],
            }),
            operation: 0,
          },
          ...(last
            ? [{ to: last, value: 0n, data: "0x" as Hex, operation: 0 }]
            : []),
        ])
      const exec = (batch: Hex) =>
        R.write.execTransactionWithRole([multiSendAddr, 0n, batch, 1, roleP], {
          account: member.account,
        })

      return {
        R,
        publicClient,
        memberAddr,
        roleP,
        Y,
        reverter,
        sendRevoke,
        exec,
      }
    }

    it("the revocation stands after the batch", async () => {
      const { R, publicClient, memberAddr, roleP, Y, sendRevoke, exec } =
        await setup()

      const hash = await exec(sendRevoke())
      await viem.assertions.emitWithArgs(hash, R, "RevokeRole", [
        roleP,
        memberAddr,
      ])
      await assertNotEmitted(viem, hash, R, "UpdateRole")
      assert.equal(await publicClient.getBalance({ address: Y }), 10n)
      assert.deepEqual(await R.read.membershipOf([memberAddr, roleP]), [
        false,
        0n,
        0n,
        0n,
      ])
    })

    it("a later entry reverting rolls back the revocation and the transfer", async () => {
      const {
        R,
        publicClient,
        memberAddr,
        roleP,
        Y,
        reverter,
        sendRevoke,
        exec,
      } = await setup()

      await viem.assertions.revertWithCustomError(
        exec(sendRevoke(reverter)),
        R,
        "ModuleTransactionFailed"
      )
      assert.equal(await publicClient.getBalance({ address: Y }), 0n)
      assert.equal((await R.read.membershipOf([memberAddr, roleP]))[3], 5n)
    })
  })
})
