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
import { expect } from "chai"
import { Interface, TypedDataEncoder } from "ethers"
import { network } from "hardhat"

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

const connection = await network.create()
const { ethers } = connection

const libIface = new Interface(["function signMessage(bytes message)"])

describe("Roles composition, end to end", () => {
  before(async () => {
    await deployMastercopies(ethers)
  })
  after(async () => {
    await connection.close()
  })

  it("a role that can make a member Safe sign raw hashes acts with that Safe's roles (ERC-1271)", async () => {
    const [ownerA, ownerM, signerS, relayer] = await ethers.getSigners()
    const lib = await (
      await ethers.getContractFactory("SignTypedMessageLib")
    ).deploy()

    // Safe A with Roles R. Safe M is a module of R with role B: send 1 ETH to Y.
    const { safe: safeA, roles: R } = await safeWithRoles(ethers, ownerA)
    const { safe: safeM, roles: Rm } = await safeWithRoles(ethers, ownerM)
    await ownerA.sendTransaction({ to: safeA, value: ethers.parseEther("2") })
    const Y = ethers.Wallet.createRandom().address
    const roleB = randomKey()
    await R.connect(ownerA).grantRole(safeM, roleB, 0, 0, 0)
    await R.connect(ownerA).scopeTarget(roleB, Y)
    await R.connect(ownerA).allowTarget(roleB, Y, [], ExecutionOptions.Send)

    // Safe M's own Roles Rm: role S may only make M sign messages.
    const roleS = randomKey()
    await Rm.connect(ownerM).grantRole(
      await signerS.getAddress(),
      roleS,
      0,
      0,
      0
    )
    await Rm.connect(ownerM).scopeTarget(roleS, await lib.getAddress())
    await Rm.connect(ownerM).allowFunction(
      roleS,
      await lib.getAddress(),
      libIface.getFunction("signMessage")!.selector,
      [],
      ExecutionOptions.DelegateCall
    )

    /** S makes M sign the digest of a RoleTx for R, role B: 1 ETH to Y. */
    const signedByM = async (deadline: bigint) => {
      const message = {
        to: Y,
        value: ethers.parseEther("1"),
        data: "0x",
        operation: 0,
        roleKey: roleB,
        salt: randomKey(),
        deadline,
      }
      const digest = TypedDataEncoder.hash(
        {
          chainId: (await ethers.provider.getNetwork()).chainId,
          verifyingContract: await R.getAddress(),
        },
        ROLE_TX_TYPES,
        message
      )
      await Rm.connect(signerS).execTransactionWithRole(
        await lib.getAddress(),
        0,
        libIface.encodeFunctionData("signMessage", [digest]),
        1,
        roleS
      )
      return message
    }

    // Anyone relays it with M's contract signature (address, empty payload).
    const message = await signedByM(NO_DEADLINE)
    await R.connect(relayer).execTransactionWithRoleSigned(message, safeM)
    expect(await ethers.provider.getBalance(Y)).to.equal(ethers.parseEther("1"))

    // M's approval of the digest stays, but the digest is used once.
    await expect(
      R.connect(relayer).execTransactionWithRoleSigned(message, safeM)
    ).to.be.revertedWithCustomError(R, "HashAlreadyConsumed")

    // An approved digest past its deadline moves nothing.
    const expired = await signedByM(
      BigInt((await ethers.provider.getBlock("latest"))!.timestamp)
    )
    await expect(
      R.connect(relayer).execTransactionWithRoleSigned(expired, safeM)
    ).to.be.revertedWithCustomError(R, "SignatureExpired")
    expect(await ethers.provider.getBalance(Y)).to.equal(ethers.parseEther("1"))
  })

  describe("settlement re-accrues allowances from storage after the executed batch", () => {
    /** Role P sends ether to Y within allowance K, and may call
     *  R.setAllowance; the Safe owns R. */
    async function setup() {
      const [ownerA, member] = await ethers.getSigners()
      const { safe: safeA, roles: R } = await safeWithRoles(ethers, ownerA)
      const Raddr = await R.getAddress()
      await ownerA.sendTransaction({ to: safeA, value: ethers.parseEther("1") })

      const multiSendAddr = await deployMultiSend(ethers, R.connect(ownerA))

      const K = randomKey()
      const roleP = randomKey()
      const Y = ethers.Wallet.createRandom().address
      await R.connect(ownerA).grantRole(
        await member.getAddress(),
        roleP,
        0,
        0,
        0
      )
      await R.connect(ownerA).setDefaultRole(await member.getAddress(), roleP)
      await R.connect(ownerA).scopeTarget(roleP, Y)
      await R.connect(ownerA).allowTarget(
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
        ExecutionOptions.Send
      )
      await R.connect(ownerA).scopeTarget(roleP, Raddr)
      await R.connect(ownerA).allowFunction(
        roleP,
        Raddr,
        R.interface.getFunction("setAllowance")!.selector,
        [],
        ExecutionOptions.None
      )

      /** A batch setting K to `balance`, then sending 10 to Y. */
      const setThenSend = (balance: number) =>
        encodeMultiSend([
          {
            to: Raddr,
            value: 0n,
            data: R.interface.encodeFunctionData("setAllowance", [
              K,
              balance,
              0,
              0,
              0,
              0,
            ]),
            operation: 0,
          },
          { to: Y, value: 10n, data: "0x", operation: 0 },
        ])

      return {
        ownerA,
        member,
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
        safeA,
        R,
        multiSendAddr,
        K,
        roleP,
        Y,
        setThenSend,
      } = await setup()
      await R.connect(ownerA).setAllowance(K, 100, 0, 0, 0, 0)
      await R.connect(ownerA).transferOwnership(safeA)

      await expect(
        R.connect(member).execTransactionWithRole(
          multiSendAddr,
          0,
          setThenSend(0),
          1,
          roleP
        )
      )
        .to.be.revertedWithCustomError(R, "AllowanceExceeded")
        .withArgs(K)
      // settlement reverts: no `false` from the IAvatar entrypoint either
      await expect(
        R.connect(member).execTransactionFromModule(
          multiSendAddr,
          0,
          setThenSend(0),
          1
        )
      )
        .to.be.revertedWithCustomError(R, "AllowanceExceeded")
        .withArgs(K)
      expect(await ethers.provider.getBalance(Y)).to.equal(0n)
      expect((await R.allowances(K)).balance).to.equal(100n)
    })

    it("deducts from the balance the batch set, not the one before it", async () => {
      const {
        ownerA,
        member,
        safeA,
        R,
        multiSendAddr,
        K,
        roleP,
        Y,
        setThenSend,
      } = await setup()
      await R.connect(ownerA).setAllowance(K, 100, 0, 0, 0, 0)
      await R.connect(ownerA).transferOwnership(safeA)

      // 50 - 10, not 100 - 10
      await R.connect(member).execTransactionWithRole(
        multiSendAddr,
        0,
        setThenSend(50),
        1,
        roleP
      )
      expect(await ethers.provider.getBalance(Y)).to.equal(10n)
      expect((await R.allowances(K)).balance).to.equal(40n)
    })

    it("authorizes against the balance before execution, which a raise in the batch cannot help", async () => {
      const {
        ownerA,
        member,
        safeA,
        R,
        multiSendAddr,
        K,
        roleP,
        Y,
        setThenSend,
      } = await setup()
      await R.connect(ownerA).setAllowance(K, 5, 0, 0, 0, 0)
      await R.connect(ownerA).transferOwnership(safeA)

      await expect(
        R.connect(member).execTransactionWithRole(
          multiSendAddr,
          0,
          setThenSend(100),
          1,
          roleP
        )
      ).to.be.revertedWithCustomError(R, "ConditionViolation")
      expect(await ethers.provider.getBalance(Y)).to.equal(0n)
      expect((await R.allowances(K)).balance).to.equal(5n)
    })
  })

  describe("settlement does not restore a limited membership the executed batch revoked", () => {
    /** Role P (5 uses) sends ether to Y and may call R.revokeRole; the Safe
     *  owns R. */
    async function setup() {
      const [ownerA, member] = await ethers.getSigners()
      const { safe: safeA, roles: R } = await safeWithRoles(ethers, ownerA)
      const Raddr = await R.getAddress()
      await ownerA.sendTransaction({ to: safeA, value: ethers.parseEther("1") })

      const multiSendAddr = await deployMultiSend(ethers, R.connect(ownerA))
      const reverter = await (
        await (await ethers.getContractFactory("Reverter")).deploy()
      ).getAddress()

      const roleP = randomKey()
      const memberAddr = await member.getAddress()
      const Y = ethers.Wallet.createRandom().address
      await R.connect(ownerA).grantRole(memberAddr, roleP, 0, 0, 5)
      for (const t of [Y, reverter]) {
        await R.connect(ownerA).scopeTarget(roleP, t)
        await R.connect(ownerA).allowTarget(roleP, t, [], ExecutionOptions.Send)
      }
      await R.connect(ownerA).scopeTarget(roleP, Raddr)
      await R.connect(ownerA).allowFunction(
        roleP,
        Raddr,
        R.interface.getFunction("revokeRole")!.selector,
        [],
        ExecutionOptions.None
      )
      await R.connect(ownerA).transferOwnership(safeA)

      /** A batch sending 10 to Y and revoking the member's role, then
       *  calling `last` if given. */
      const sendRevoke = (last?: string) =>
        encodeMultiSend([
          { to: Y, value: 10n, data: "0x", operation: 0 },
          {
            to: Raddr,
            value: 0n,
            data: R.interface.encodeFunctionData("revokeRole", [
              memberAddr,
              roleP,
            ]),
            operation: 0,
          },
          ...(last ? [{ to: last, value: 0n, data: "0x", operation: 0 }] : []),
        ])
      const exec = (batch: string) =>
        R.connect(member).execTransactionWithRole(
          multiSendAddr,
          0,
          batch,
          1,
          roleP
        )

      return { R, memberAddr, roleP, Y, reverter, sendRevoke, exec }
    }

    it("the revocation stands after the batch", async () => {
      const { R, memberAddr, roleP, Y, sendRevoke, exec } = await setup()

      await expect(exec(sendRevoke()))
        .to.emit(R, "RevokeRole")
        .withArgs(roleP, memberAddr)
        .and.not.to.emit(R, "UpdateRole")
      expect(await ethers.provider.getBalance(Y)).to.equal(10n)
      expect(await R.membershipOf(memberAddr, roleP)).to.deep.equal([
        false,
        0n,
        0n,
        0n,
      ])
    })

    it("a later entry reverting rolls back the revocation and the transfer", async () => {
      const { R, memberAddr, roleP, Y, reverter, sendRevoke, exec } =
        await setup()

      await expect(exec(sendRevoke(reverter))).to.be.revertedWithCustomError(
        R,
        "ModuleTransactionFailed"
      )
      expect(await ethers.provider.getBalance(Y)).to.equal(0n)
      expect((await R.membershipOf(memberAddr, roleP)).usesLeft).to.equal(5n)
    })
  })
})
