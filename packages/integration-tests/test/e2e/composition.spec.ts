/**
 * End-to-end composition of Roles v3 with real Safes (1.4.1, with the
 * CompatibilityFallbackHandler), SignTypedMessageLib and MultiSend.
 *
 * Each case shows how authority or state flows across contracts, not what one
 * function does on its own. They pin down documented behaviour:
 * - a signature of a Safe counts wherever its EIP-1271 signature does, so a
 *   role that can make it sign raw hashes acts with that Safe's roles
 *   (docs: general/signing, "What a signature authorizes");
 * - settlement writes after execution, so it overwrites allowance and
 *   membership changes the executed transaction made (docs: general/
 *   allowances and general/membership).
 */
import { expect } from "chai"
import {
  AbiCoder,
  Interface,
  TypedDataEncoder,
  ZeroAddress,
  ZeroHash,
  concat,
  hexlify,
  randomBytes,
  solidityPacked,
} from "ethers"
import type { Signer } from "ethers"
import { network } from "hardhat"

import { iface as ifaceSafe } from "../eip712/setup/deploy-mastercopies/safeMastercopy.js"
import { deploySafe } from "../eip712/setup/safe.js"
import deployMastercopies from "../eip712/setup/deploy-mastercopies/index.js"

const connection = await network.create()
const { ethers } = connection

const abi = AbiCoder.defaultAbiCoder()

const Encoding = { None: 0, Static: 1, EtherValue: 6 } as const
const Operator = { Pass: 0, WithinAllowance: 28 } as const
const ExecutionOptions = { None: 0, Send: 1, DelegateCall: 2, Both: 3 }

const libIface = new Interface(["function signMessage(bytes message)"])
const multiSendIface = new Interface(["function multiSend(bytes transactions)"])

const randomKey = () => hexlify(randomBytes(32))

async function deployRoles(owner: string, avatar: string) {
  const lib = async (name: string) =>
    (await (await ethers.getContractFactory(name)).deploy()).getAddress()
  const libraries = {
    ConditionStorer: await lib("ConditionStorer"),
    WithinRatioChecker: await lib("WithinRatioChecker"),
    CustomConditionChecker: await lib("CustomConditionChecker"),
  }
  const factory = await ethers.getContractFactory("Roles", { libraries })
  const roles = await factory.deploy(owner, avatar, avatar)
  return roles
}

/** `owner` (threshold 1) executes a call from the Safe. */
async function execSafe(
  owner: Signer,
  safe: string,
  to: string,
  data: string,
  operation = 0,
  value = 0n
) {
  const approval = concat([
    abi.encode(["address"], [await owner.getAddress()]),
    ZeroHash,
    "0x01",
  ])
  return owner.sendTransaction({
    to: safe,
    data: ifaceSafe.encodeFunctionData("execTransaction", [
      to,
      value,
      data,
      operation,
      0n,
      0n,
      0n,
      ZeroAddress,
      ZeroAddress,
      approval,
    ]),
  })
}

/** A Safe owned by `owner`, with a Roles modifier enabled as its module. */
async function safeWithRoles(owner: Signer) {
  const safe = await deploySafe(
    {
      owners: [await owner.getAddress()],
      threshold: 1,
      creationNonce: BigInt(randomKey()),
    },
    owner as any
  )
  const roles = await deployRoles(await owner.getAddress(), safe)
  await execSafe(
    owner,
    safe,
    safe,
    ifaceSafe.encodeFunctionData("enableModule", [await roles.getAddress()])
  )
  return { safe, roles }
}

const encodeMultiSend = (
  txs: { to: string; value: bigint; data: string; operation: number }[]
) =>
  multiSendIface.encodeFunctionData("multiSend", [
    concat(
      txs.map((t) =>
        solidityPacked(
          ["uint8", "address", "uint256", "uint256", "bytes"],
          [t.operation, t.to, t.value, (t.data.length - 2) / 2, t.data]
        )
      )
    ),
  ])

describe("Roles composition, end to end", () => {
  after(async () => {
    await connection.close()
  })

  it("a role that can make a member Safe sign raw hashes acts with that Safe's roles (ERC-1271)", async () => {
    await deployMastercopies(ethers)
    const [ownerA, ownerM, signerS, relayer] = await ethers.getSigners()
    const lib = await (
      await ethers.getContractFactory("SignTypedMessageLib")
    ).deploy()

    // Safe A with Roles R. Safe M is a module of R with role B: send 1 ETH to Y.
    const { safe: safeA, roles: R } = await safeWithRoles(ownerA)
    const { safe: safeM, roles: Rm } = await safeWithRoles(ownerM)
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

    // S makes M sign the digest of a RoleTx for R, role B.
    const salt = randomKey()
    const message = {
      to: Y,
      value: ethers.parseEther("1"),
      data: "0x",
      operation: 0,
      roleKey: roleB,
      shouldRevert: true,
      salt,
    }
    const digest = TypedDataEncoder.hash(
      {
        chainId: (await ethers.provider.getNetwork()).chainId,
        verifyingContract: await R.getAddress(),
      },
      {
        RoleTx: [
          { name: "to", type: "address" },
          { name: "value", type: "uint256" },
          { name: "data", type: "bytes" },
          { name: "operation", type: "uint8" },
          { name: "roleKey", type: "bytes32" },
          { name: "shouldRevert", type: "bool" },
          { name: "salt", type: "bytes32" },
        ],
      },
      message
    )
    await Rm.connect(signerS).execTransactionWithRole(
      await lib.getAddress(),
      0,
      libIface.encodeFunctionData("signMessage", [digest]),
      1,
      roleS,
      true
    )

    // Anyone relays it with M's contract signature (address, empty payload).
    await R.connect(relayer).execTransactionWithSignature(
      message.to,
      message.value,
      message.data,
      message.operation,
      message.roleKey,
      message.shouldRevert,
      message.salt,
      safeM
    )
    expect(await ethers.provider.getBalance(Y)).to.equal(ethers.parseEther("1"))
  })

  it("settlement overwrites an allowance the executed batch set", async () => {
    await deployMastercopies(ethers)
    const [ownerA, member] = await ethers.getSigners()
    const { safe: safeA, roles: R } = await safeWithRoles(ownerA)
    const Raddr = await R.getAddress()
    await ownerA.sendTransaction({ to: safeA, value: ethers.parseEther("1") })

    const multiSend = await (
      await ethers.getContractFactory("MultiSend")
    ).deploy()
    const unwrapper = await (
      await ethers.getContractFactory("MultiSendUnwrapper")
    ).deploy()
    await R.connect(ownerA).setTransactionUnwrapper(
      await multiSend.getAddress(),
      multiSendIface.getFunction("multiSend")!.selector,
      await unwrapper.getAddress()
    )

    // Role P: send ether to Y within allowance K, and call R.setAllowance.
    const K = randomKey()
    const roleP = randomKey()
    const Y = ethers.Wallet.createRandom().address
    await R.connect(ownerA).setAllowance(K, 100, 0, 0, 0, 0)
    await R.connect(ownerA).grantRole(await member.getAddress(), roleP, 0, 0, 0)
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
    // the Safe owns R from here on
    await R.connect(ownerA).transferOwnership(safeA)

    const batch = encodeMultiSend([
      {
        to: R.target as string,
        value: 0n,
        data: R.interface.encodeFunctionData("setAllowance", [
          K,
          0,
          0,
          0,
          0,
          0,
        ]),
        operation: 0,
      },
      { to: Y, value: 10n, data: "0x", operation: 0 },
    ])
    await R.connect(member).execTransactionWithRole(
      await multiSend.getAddress(),
      0,
      batch,
      1,
      roleP,
      true
    )

    // In order, the batch sets K to 0 and then spends 10 from it, which
    // should not pass. Both ran, and settlement wrote 100 - 10.
    expect(await ethers.provider.getBalance(Y)).to.equal(10n)
    expect((await R.allowances(K)).balance).to.equal(90n)
  })

  it("settlement restores a limited membership the executed call revoked", async () => {
    await deployMastercopies(ethers)
    const [ownerA, member] = await ethers.getSigners()
    const { safe: safeA, roles: R } = await safeWithRoles(ownerA)
    const Raddr = await R.getAddress()
    const roleP = randomKey()
    const memberAddr = await member.getAddress()
    await R.connect(ownerA).grantRole(memberAddr, roleP, 0, 0, 5)
    await R.connect(ownerA).scopeTarget(roleP, Raddr)
    await R.connect(ownerA).allowFunction(
      roleP,
      Raddr,
      R.interface.getFunction("revokeRole")!.selector,
      [],
      ExecutionOptions.None
    )
    await R.connect(ownerA).transferOwnership(safeA)

    await R.connect(member).execTransactionWithRole(
      Raddr,
      0,
      R.interface.encodeFunctionData("revokeRole", [memberAddr, roleP]),
      0,
      roleP,
      true
    )
    // revoked by the call, restored (with one use less) by settlement
    expect(await R.isMember(roleP, memberAddr)).to.equal(true)
  })
})
