import { expect } from "chai";
import { hexlify, Interface, randomBytes, ZeroAddress, ZeroHash } from "ethers";
import { network } from "hardhat";

import {
  ConditionViolationStatus,
  Encoding,
  ExecutionOptions,
  flattenCondition,
  Operator,
} from "./utils.js";
import { createSetup } from "./setup.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { deployEvaluator, deployRolesMod } = createSetup(connection);

const iface = new Interface([
  "function doNothing()",
  "function oneParamStatic(uint256)",
  "function fn(address)",
]);

const ROLE_TX_TYPES = {
  RoleTx: [
    { name: "to", type: "address" },
    { name: "value", type: "uint256" },
    { name: "data", type: "bytes" },
    { name: "operation", type: "uint8" },
    { name: "roleKey", type: "bytes32" },
    { name: "shouldRevert", type: "bool" },
    { name: "salt", type: "bytes32" },
  ],
};

describe("Core / Evaluator split", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [owner, member, nonMember, relayer] = await ethers.getSigners();

    const Avatar = await ethers.getContractFactory("TestAvatar");
    const avatar = await Avatar.deploy();
    const avatarAddress = await avatar.getAddress();

    const TestContract = await ethers.getContractFactory("TestContract");
    const testContract = await TestContract.deploy();
    const testContractAddress = await testContract.getAddress();

    const evaluator = await deployEvaluator();
    const evaluatorAddress = await evaluator.getAddress();

    const roles = await deployRolesMod(
      owner.address,
      avatarAddress,
      avatarAddress,
      evaluatorAddress,
    );

    const roleKey = hexlify(randomBytes(32));

    await roles.connect(owner).grantRole(member.address, roleKey, 0, 0, 0);
    await roles.connect(owner).setDefaultRole(member.address, roleKey);
    await roles.connect(owner).scopeTarget(roleKey, testContractAddress);

    return {
      owner,
      member,
      nonMember,
      relayer,
      avatar,
      avatarAddress,
      testContract,
      testContractAddress,
      evaluator,
      evaluatorAddress,
      roles: roles.connect(owner),
      roleKey,
    };
  }

  describe("evaluator configuration & hot-swapping", () => {
    it("sets the initial evaluator during deployment and emits SetEvaluator", async () => {
      const { owner, avatarAddress, evaluatorAddress } =
        await loadFixture(setup);

      const roles = await deployRolesMod(
        owner.address,
        avatarAddress,
        avatarAddress,
        evaluatorAddress,
      );

      expect(await roles.evaluator()).to.equal(evaluatorAddress);
      await expect(roles.deploymentTransaction())
        .to.emit(roles, "SetEvaluator")
        .withArgs(evaluatorAddress);
    });

    it("reverts ZeroAddressNotAllowed if initial evaluator is address(0)", async () => {
      const { owner, avatarAddress } = await loadFixture(setup);

      await expect(
        deployRolesMod(
          owner.address,
          avatarAddress,
          avatarAddress,
          ZeroAddress,
        ),
      ).to.be.revertedWithCustomError(
        await ethers.getContractFactory("Roles"),
        "ZeroAddressNotAllowed",
      );
    });

    it("allows owner to swap evaluator, emits SetEvaluator, and rejects zero address", async () => {
      const { roles, owner, nonMember } = await loadFixture(setup);

      const alt = await deployEvaluator();
      const altAddress = await alt.getAddress();

      await expect(
        roles.connect(owner).setEvaluator(ZeroAddress),
      ).to.be.revertedWithCustomError(roles, "ZeroAddressNotAllowed");

      await expect(
        roles.connect(nonMember).setEvaluator(altAddress),
      ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");

      await expect(roles.connect(owner).setEvaluator(altAddress))
        .to.emit(roles, "SetEvaluator")
        .withArgs(altAddress);

      expect(await roles.evaluator()).to.equal(altAddress);
    });

    it("swaps evaluator on an existing mod with no redeploy and preserves all state", async () => {
      const {
        roles,
        owner,
        member,
        testContractAddress,
        roleKey,
        evaluatorAddress,
      } = await loadFixture(setup);

      const selector = iface.getFunction("oneParamStatic")!.selector;
      const allowanceKey = ethers.id("HOT_SWAP_ALLOWANCE");

      await roles.setAllowance(allowanceKey, 100, 0, 0, 0, 0);
      await roles.allowFunction(
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.WithinAllowance,
              compValue: allowanceKey,
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // Works with initial evaluator and consumes 40
      await roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData("oneParamStatic", [40]),
          0,
        );
      expect((await roles.allowances(allowanceKey)).balance).to.equal(60);

      // Swap to always-deny evaluator: same permission now fails without redeploying Core
      const Deny = await ethers.getContractFactory("TestAlwaysDenyEvaluator");
      const deny = await Deny.deploy();
      await roles.connect(owner).setEvaluator(await deny.getAddress());

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [10]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 7, 4);

      // Swap back to a freshly deployed real Evaluator: membership, permission, and allowance balance (60) remain intact
      const fresh = await deployEvaluator();
      expect(await fresh.getAddress()).to.not.equal(evaluatorAddress);
      await roles.connect(owner).setEvaluator(await fresh.getAddress());

      // 70 > remaining 60 fails
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [70]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "ConditionViolation");

      // 60 <= remaining 60 succeeds
      await roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData("oneParamStatic", [60]),
          0,
        );
      expect((await roles.allowances(allowanceKey)).balance).to.equal(0);
    });

    it("reverts EvaluatorNotAContract if evaluator has no code", async () => {
      const { roles, owner, member, nonMember, testContractAddress, roleKey } =
        await loadFixture(setup);

      await roles.allowTargetPacked(
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );
      await roles.connect(owner).setEvaluator(nonMember.address);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "EvaluatorNotAContract")
        .withArgs(nonMember.address);

      await expect(
        roles.packConditions([
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithoutReason(ethers);
    });

    it("delegates integrity validation and packing to the installed Evaluator", async () => {
      const { roles, owner, testContractAddress, roleKey } =
        await loadFixture(setup);

      const Reverting = await ethers.getContractFactory(
        "TestRevertingEvaluator",
      );
      const reverting = await Reverting.deploy();
      await roles.connect(owner).setEvaluator(await reverting.getAddress());

      const conditions = flattenCondition({
        paramType: Encoding.None,
        operator: Operator.Pass,
      });

      await expect(
        roles.packConditions(conditions),
      ).to.be.revertedWithCustomError(reverting, "IntentionalEvaluatorRevert");

      await expect(
        roles.allowTarget(
          roleKey,
          testContractAddress,
          conditions,
          ExecutionOptions.None,
        ),
      ).to.be.revertedWithCustomError(reverting, "IntentionalEvaluatorRevert");

      // Empty conditions bypass packing and store an opaque empty buffer
      expect(await roles.packConditions([])).to.equal("0x");
      await expect(
        roles.allowTarget(
          roleKey,
          testContractAddress,
          [],
          ExecutionOptions.None,
        ),
      ).to.not.be.revert(ethers);
    });
  });

  describe("non-member invariant (independent of Evaluator)", () => {
    async function setupWithAlwaysAllowEvaluator() {
      const ctx = await setup();
      const AlwaysAllow = await ethers.getContractFactory(
        "TestAlwaysAllowEvaluator",
      );
      const alwaysAllow = await AlwaysAllow.deploy();
      await ctx.roles
        .connect(ctx.owner)
        .setEvaluator(await alwaysAllow.getAddress());

      await ctx.roles.allowTargetPacked(
        ctx.roleKey,
        ctx.testContractAddress,
        "0x",
        ExecutionOptions.Both,
      );

      return { ...ctx, alwaysAllow };
    }

    it("blocks a non-enabled caller even when Evaluator always approves", async () => {
      const { roles, nonMember, testContractAddress, roleKey } =
        await loadFixture(setupWithAlwaysAllowEvaluator);

      const data = iface.encodeFunctionData("doNothing");

      await expect(
        roles
          .connect(nonMember)
          .execTransactionFromModule(testContractAddress, 0, data, 0),
      ).to.be.revertedWithCustomError(roles, "NotAuthorized");

      await expect(
        roles
          .connect(nonMember)
          .execTransactionFromModuleReturnData(testContractAddress, 0, data, 0),
      ).to.be.revertedWithCustomError(roles, "NotAuthorized");

      await expect(
        roles
          .connect(nonMember)
          .execTransactionWithRole(
            testContractAddress,
            0,
            data,
            0,
            roleKey,
            true,
          ),
      ).to.be.revertedWithCustomError(roles, "NotAuthorized");
    });

    it("blocks an enabled module with no role membership across all entrypoints", async () => {
      const { roles, owner, nonMember, relayer, testContractAddress, roleKey } =
        await loadFixture(setupWithAlwaysAllowEvaluator);

      await roles.connect(owner).enableModule(nonMember.address);
      await roles.connect(owner).setDefaultRole(nonMember.address, roleKey);

      const data = iface.encodeFunctionData("doNothing");

      await expect(
        roles
          .connect(nonMember)
          .execTransactionFromModule(testContractAddress, 0, data, 0),
      ).to.be.revertedWithCustomError(roles, "NoMembership");

      await expect(
        roles
          .connect(nonMember)
          .execTransactionFromModuleReturnData(testContractAddress, 0, data, 0),
      ).to.be.revertedWithCustomError(roles, "NoMembership");

      await expect(
        roles
          .connect(nonMember)
          .execTransactionWithRole(
            testContractAddress,
            0,
            data,
            0,
            roleKey,
            true,
          ),
      ).to.be.revertedWithCustomError(roles, "NoMembership");

      // Relayed execTransactionWithSignature signed by enabled non-member
      const chainId = (await ethers.provider.getNetwork()).chainId;
      const domain = {
        chainId,
        verifyingContract: await roles.getAddress(),
      };
      const salt = hexlify(randomBytes(32));
      const signature = await nonMember.signTypedData(domain, ROLE_TX_TYPES, {
        to: testContractAddress,
        value: 0,
        data,
        operation: 0,
        roleKey,
        shouldRevert: true,
        salt,
      });

      await expect(
        roles
          .connect(relayer)
          .execTransactionWithSignature(
            testContractAddress,
            0,
            data,
            0,
            roleKey,
            true,
            salt,
            signature,
          ),
      ).to.be.revertedWithCustomError(roles, "NoMembership");
    });

    it("enforces zero role, validity window, and finite uses even with an always-allow Evaluator", async () => {
      const { roles, owner, nonMember, testContractAddress, roleKey } =
        await loadFixture(setupWithAlwaysAllowEvaluator);

      const data = iface.encodeFunctionData("doNothing");

      // Zero role is always rejected
      await roles
        .connect(owner)
        .grantRole(nonMember.address, ZeroHash, 0, 0, 0);
      await expect(
        roles
          .connect(nonMember)
          .execTransactionWithRole(
            testContractAddress,
            0,
            data,
            0,
            ZeroHash,
            true,
          ),
      ).to.be.revertedWithCustomError(roles, "NoMembership");

      // Future start timestamp rejected
      const now = await time.latest();
      await roles
        .connect(owner)
        .grantRole(nonMember.address, roleKey, now + 1000, now + 2000, 1);

      await expect(
        roles
          .connect(nonMember)
          .execTransactionWithRole(
            testContractAddress,
            0,
            data,
            0,
            roleKey,
            true,
          ),
      ).to.be.revertedWithCustomError(roles, "MembershipNotYetValid");

      // Advance into window: 1 use succeeds, 2nd call rejected
      await time.increaseTo(now + 1000);
      await roles
        .connect(nonMember)
        .execTransactionWithRole(
          testContractAddress,
          0,
          data,
          0,
          roleKey,
          true,
        );

      await expect(
        roles
          .connect(nonMember)
          .execTransactionWithRole(
            testContractAddress,
            0,
            data,
            0,
            roleKey,
            true,
          ),
      ).to.be.revertedWithCustomError(roles, "NoMembership");

      // Expired membership rejected
      await roles
        .connect(owner)
        .grantRole(nonMember.address, roleKey, now, now + 1500, 0);
      await time.increaseTo(now + 1501);
      await expect(
        roles
          .connect(nonMember)
          .execTransactionWithRole(
            testContractAddress,
            0,
            data,
            0,
            roleKey,
            true,
          ),
      ).to.be.revertedWithCustomError(roles, "MembershipExpired");
    });
  });

  describe("Core invariants independent of Evaluator", () => {
    it("enforces scopeConfig lookup, ExecutionOptions, and short calldata even with always-allow Evaluator", async () => {
      const { roles, owner, member, avatar, testContractAddress, roleKey } =
        await loadFixture(setup);

      const AlwaysAllow = await ethers.getContractFactory(
        "TestAlwaysAllowEvaluator",
      );
      const alwaysAllow = await AlwaysAllow.deploy();
      await roles.connect(owner).setEvaluator(await alwaysAllow.getAddress());

      // Unpermitted selector still reverts TransactionNotAllowed
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");

      // Allow target with ExecutionOptions.None
      await roles.allowTargetPacked(
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      // 1-3 byte calldata still reverts FunctionSignatureTooShort
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x1234", 0),
      ).to.be.revertedWithCustomError(roles, "FunctionSignatureTooShort");

      // ETH value still reverts SendNotAllowed
      await owner.sendTransaction({
        to: await avatar.getAddress(),
        value: ethers.parseEther("1"),
      });
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            ethers.parseEther("0.1"),
            "0x",
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "SendNotAllowed");

      // DelegateCall still reverts DelegateCallNotAllowed
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 1),
      ).to.be.revertedWithCustomError(roles, "DelegateCallNotAllowed");
    });

    it("invokes Evaluator via STATICCALL so a state-mutating Evaluator reverts", async () => {
      const { roles, owner, member, testContractAddress, roleKey } =
        await loadFixture(setup);

      const Mutating = await ethers.getContractFactory("TestMutatingEvaluator");
      const mutating = await Mutating.deploy();
      await roles.connect(owner).setEvaluator(await mutating.getAddress());
      await roles.allowTargetPacked(
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      ).to.be.revert(ethers);

      expect(await mutating.counter()).to.equal(0);
    });

    it("propagates Evaluator reverts and rejects malformed return data", async () => {
      const { roles, owner, member, testContractAddress, roleKey } =
        await loadFixture(setup);

      await roles.allowTargetPacked(
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      const Reverting = await ethers.getContractFactory(
        "TestRevertingEvaluator",
      );
      const reverting = await Reverting.deploy();
      await roles.connect(owner).setEvaluator(await reverting.getAddress());

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      ).to.be.revertedWithCustomError(reverting, "IntentionalEvaluatorRevert");

      const Malformed = await ethers.getContractFactory(
        "TestMalformedReturnEvaluator",
      );
      const malformed = await Malformed.deploy();
      await roles.connect(owner).setEvaluator(await malformed.getAddress());

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      ).to.be.revert(ethers);
    });

    it("prevents a forging Evaluator from inflating or overspending allowances during settlement", async () => {
      const { roles, owner, member, testContractAddress, roleKey } =
        await loadFixture(setup);

      const Forging = await ethers.getContractFactory(
        "TestForgingConsumptionEvaluator",
      );
      const forging = await Forging.deploy();
      await roles.connect(owner).setEvaluator(await forging.getAddress());
      await roles.allowTargetPacked(
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      const allowanceKey = ethers.id("FORGE_TEST");
      await roles.setAllowance(allowanceKey, 100, 0, 0, 0, 0);

      // 1. Forged huge balance with 0 consumed cannot inflate Core's allowance balance
      await forging.setForged([
        {
          allowanceKey,
          balance: 999999n,
          consumed: 0n,
          timestamp: 12345n,
        },
      ]);
      await roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData("doNothing"),
          0,
        );
      expect((await roles.allowances(allowanceKey)).balance).to.equal(100);

      // 2. Forged consumed > real balance reverts even if forged balance claims enough
      await forging.setForged([
        {
          allowanceKey,
          balance: 999999n,
          consumed: 101n,
          timestamp: 0n,
        },
      ]);
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "AllowanceExceeded")
        .withArgs(allowanceKey);

      // 3. Duplicate entries whose sum exceeds real balance revert
      await forging.setForged([
        { allowanceKey, balance: 100n, consumed: 60n, timestamp: 0n },
        { allowanceKey, balance: 100n, consumed: 60n, timestamp: 0n },
      ]);
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "AllowanceExceeded")
        .withArgs(allowanceKey);

      expect((await roles.allowances(allowanceKey)).balance).to.equal(100);
    });

    it("handles unknown uint8 Status, Operator, and Encoding values from a future Evaluator without Panic(0x21)", async () => {
      const { roles, evaluator, owner, member, testContractAddress, roleKey } =
        await loadFixture(setup);

      // Current Evaluator bounds-checks raw uint8 values cleanly (not Panic 0x21)
      await expect(
        roles.packConditions([
          {
            parent: 0,
            paramType: 99,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      )
        .to.be.revertedWithCustomError(evaluator, "UnsuitableParameterType")
        .withArgs(0);

      await expect(
        roles.packConditions([
          {
            parent: 0,
            paramType: Encoding.None,
            operator: 99,
            compValue: "0x",
          },
        ]),
      )
        .to.be.revertedWithCustomError(evaluator, "UnsupportedOperator")
        .withArgs(0);

      // Install a future Evaluator that accepts new Encoding/Operator codes
      // and returns a new Status code (200)
      const Future = await ethers.getContractFactory("TestFutureEvaluator");
      const future = await Future.deploy();
      await roles.connect(owner).setEvaluator(await future.getAddress());

      const futureConditions = [
        {
          parent: 0,
          paramType: 99,
          operator: 200,
          compValue: "0x",
        },
      ];

      expect(await roles.packConditions(futureConditions)).to.equal("0x63c8");

      await expect(
        roles.allowTarget(
          roleKey,
          testContractAddress,
          futureConditions,
          ExecutionOptions.None,
        ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(200, 3, 36);
    });
  });

  describe("shared stateless Evaluator across multiple Core instances", () => {
    it("isolates avatar and allowance state per Core when sharing one Evaluator", async () => {
      const { owner, member, testContractAddress, evaluatorAddress } =
        await loadFixture(setup);

      const Avatar = await ethers.getContractFactory("TestAvatar");
      const avatar1 = await Avatar.deploy();
      const avatar2 = await Avatar.deploy();
      const avatar1Address = await avatar1.getAddress();
      const avatar2Address = await avatar2.getAddress();

      const roles1 = await deployRolesMod(
        owner.address,
        avatar1Address,
        avatar1Address,
        evaluatorAddress,
      );
      const roles2 = await deployRolesMod(
        owner.address,
        avatar2Address,
        avatar2Address,
        evaluatorAddress,
      );

      const roleKey = ethers.id("SHARED_ROLE");
      const allowanceKey = ethers.id("SHARED_ALLOWANCE");
      const fnAddrSelector = iface.getFunction("fn")!.selector;
      const fnUintSelector = iface.getFunction("oneParamStatic")!.selector;

      for (const mod of [roles1, roles2]) {
        await mod.connect(owner).grantRole(member.address, roleKey, 0, 0, 0);
        await mod.connect(owner).setDefaultRole(member.address, roleKey);
        await mod.connect(owner).scopeTarget(roleKey, testContractAddress);
        await mod.connect(owner).allowFunction(
          roleKey,
          testContractAddress,
          fnAddrSelector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Static,
                operator: Operator.EqualToAvatar,
              },
            ],
          }),
          ExecutionOptions.None,
        );
        await mod.connect(owner).allowFunction(
          roleKey,
          testContractAddress,
          fnUintSelector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Static,
                operator: Operator.WithinAllowance,
                compValue: allowanceKey,
              },
            ],
          }),
          ExecutionOptions.None,
        );
      }

      // Different allowance balances on roles1 (50) and roles2 (200)
      await roles1.connect(owner).setAllowance(allowanceKey, 50, 0, 0, 0, 0);
      await roles2.connect(owner).setAllowance(allowanceKey, 200, 0, 0, 0, 0);

      // EqualToAvatar checks each Core's own avatar
      await roles1
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData("fn", [avatar1Address]),
          0,
        );
      await expect(
        roles1
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("fn", [avatar2Address]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles1, "ConditionViolation");

      await roles2
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData("fn", [avatar2Address]),
          0,
        );
      await expect(
        roles2
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("fn", [avatar1Address]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles2, "ConditionViolation");

      // WithinAllowance reads and settles each Core's own allowance balance
      await expect(
        roles1
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [100]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles1, "ConditionViolation");

      await roles2
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData("oneParamStatic", [100]),
          0,
        );

      expect((await roles1.allowances(allowanceKey)).balance).to.equal(50);
      expect((await roles2.allowances(allowanceKey)).balance).to.equal(100);
    });
  });
});
