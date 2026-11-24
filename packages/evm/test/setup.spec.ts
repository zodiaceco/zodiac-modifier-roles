import { expect } from "chai";
import { ZeroHash, ZeroAddress, Interface } from "ethers";
import { network } from "hardhat";

import {
  Encoding,
  ExecutionOptions,
  Operator,
  packConditions,
  maxUint64,
  maxUint128,
} from "./utils.js";
import { createSetup } from "./setup.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { deployEvaluator, deployRolesMod } = createSetup(connection);

const iface = new Interface([
  "function doNothing()",
  "function doEvenLess()",
  "function oneParamStatic(uint256)",
  "function other()",
]);

/**
 * Setup tests
 *
 * Scope: Configuration API.
 *
 * This file verifies the functionality of the module's configuration interface:
 * - Role Management: Granting, revoking, and assigning roles.
 * - Permission Management: Defining and managing permissions for targets and functions.
 * - Allowance Configuration: Setting and updating allowance parameters.
 * - Adapter Management: Registering and removing transaction unwrappers.
 *
 * It ensures that configuration changes are correctly applied to storage and that relevant events are emitted.
 */

describe("Setup", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [owner, member] = await ethers.getSigners();

    const Avatar = await ethers.getContractFactory("TestAvatar");
    const avatar = await Avatar.deploy();
    const avatarAddress = await avatar.getAddress();

    const evaluator = await deployEvaluator();
    const roles = await deployRolesMod(
      owner.address,
      avatarAddress,
      avatarAddress,
      await evaluator.getAddress(),
    );

    const TestContract = await ethers.getContractFactory("TestContract");
    const testContract = await TestContract.deploy();
    const testContractAddress = await testContract.getAddress();

    const ROLE_KEY = ethers.id("TEST_ROLE");

    return {
      roles: roles.connect(owner),
      evaluator,
      owner,
      member,
      testContract,
      testContractAddress,
      ROLE_KEY,
    };
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // ROLE MEMBERSHIP
  // ═══════════════════════════════════════════════════════════════════════════

  describe("grantRole", () => {
    it("grants role to module", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.allowTargetPacked(
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      // Member can now execute - proves role was granted
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.not.be.revert(ethers);
    });

    it("automatically enables module if not already enabled", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      expect(await roles.isModuleEnabled(member.address)).to.be.false;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);

      expect(await roles.isModuleEnabled(member.address)).to.be.true;
    });

    it("emits GrantRole event", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await expect(roles.grantRole(member.address, ROLE_KEY, 100, 200, 5))
        .to.emit(roles, "GrantRole")
        .withArgs(ROLE_KEY, member.address, 100, 200, 5);
    });

    describe("validity window", () => {
      it("sets start timestamp when start > 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await expect(roles.grantRole(member.address, ROLE_KEY, 1000, 0, 0))
          .to.emit(roles, "GrantRole")
          .withArgs(ROLE_KEY, member.address, 1000, maxUint64, maxUint128);
      });

      it("defaults to immediately valid when start = 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await expect(roles.grantRole(member.address, ROLE_KEY, 0, 0, 0))
          .to.emit(roles, "GrantRole")
          .withArgs(ROLE_KEY, member.address, 0, maxUint64, maxUint128);
      });

      it("sets end timestamp when end > 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await expect(roles.grantRole(member.address, ROLE_KEY, 0, 9999, 0))
          .to.emit(roles, "GrantRole")
          .withArgs(ROLE_KEY, member.address, 0, 9999, maxUint128);
      });

      it("defaults to never expires (max uint64) when end = 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await expect(roles.grantRole(member.address, ROLE_KEY, 0, 0, 0))
          .to.emit(roles, "GrantRole")
          .withArgs(ROLE_KEY, member.address, 0, maxUint64, maxUint128);
      });
    });

    describe("usage limits", () => {
      it("sets finite usesLeft when usesLeft > 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await expect(roles.grantRole(member.address, ROLE_KEY, 0, 0, 10))
          .to.emit(roles, "GrantRole")
          .withArgs(ROLE_KEY, member.address, 0, maxUint64, 10);
      });

      it("defaults to unlimited uses (max uint128) when usesLeft = 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await expect(roles.grantRole(member.address, ROLE_KEY, 0, 0, 0))
          .to.emit(roles, "GrantRole")
          .withArgs(ROLE_KEY, member.address, 0, maxUint64, maxUint128);
      });
    });

    it("overwrites existing membership with new parameters", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 100, 200, 5);

      await expect(roles.grantRole(member.address, ROLE_KEY, 300, 400, 10))
        .to.emit(roles, "GrantRole")
        .withArgs(ROLE_KEY, member.address, 300, 400, 10);
    });
  });

  describe("revokeRole", () => {
    it("removes membership from role", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.allowTargetPacked(
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.not.be.revert(ethers);

      await roles.revokeRole(member.address, ROLE_KEY);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.be.revertedWithCustomError(roles, "NoMembership");
    });

    it("emits RevokeRole event", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);

      await expect(roles.revokeRole(member.address, ROLE_KEY))
        .to.emit(roles, "RevokeRole")
        .withArgs(ROLE_KEY, member.address);
    });

    it("does not disable module (may have other roles)", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const ROLE_KEY_2 = ethers.id("TEST_ROLE_2");

      expect(await roles.isModuleEnabled(member.address)).to.be.false;
      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.grantRole(member.address, ROLE_KEY_2, 0, 0, 0);
      await roles.revokeRole(member.address, ROLE_KEY);
      expect(await roles.isModuleEnabled(member.address)).to.be.true;
    });

    it("succeeds even if membership doesn't exist", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await expect(roles.revokeRole(member.address, ROLE_KEY)).to.not.be.revert(
        ethers,
      );
    });
  });

  describe("renounceRole", () => {
    it("allows member to revoke their own role", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.allowTargetPacked(
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.not.be.revert(ethers);

      await roles.connect(member).renounceRole(ROLE_KEY);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.be.revertedWithCustomError(roles, "NoMembership");
    });

    it("emits RevokeRole event", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);

      await expect(roles.connect(member).renounceRole(ROLE_KEY))
        .to.emit(roles, "RevokeRole")
        .withArgs(ROLE_KEY, member.address);
    });
  });

  describe("assignRoles", () => {
    it("batch grants roles when memberOf is true", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const ROLE_KEY_2 = ethers.id("TEST_ROLE_2");

      await roles.assignRoles(
        member.address,
        [ROLE_KEY, ROLE_KEY_2],
        [true, true],
      );

      expect(await roles.isModuleEnabled(member.address)).to.be.true;
    });

    it("batch revokes roles when memberOf is false", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const ROLE_KEY_2 = ethers.id("TEST_ROLE_2");

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.grantRole(member.address, ROLE_KEY_2, 0, 0, 0);

      await expect(
        roles.assignRoles(
          member.address,
          [ROLE_KEY, ROLE_KEY_2],
          [false, false],
        ),
      )
        .to.emit(roles, "RevokeRole")
        .withArgs(ROLE_KEY, member.address);
    });

    it("handles mixed grant and revoke in single call", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const ROLE_KEY_2 = ethers.id("TEST_ROLE_2");

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);

      // Revoke ROLE_KEY, grant ROLE_KEY_2
      const tx = await roles.assignRoles(
        member.address,
        [ROLE_KEY, ROLE_KEY_2],
        [false, true],
      );

      await expect(tx)
        .to.emit(roles, "RevokeRole")
        .withArgs(ROLE_KEY, member.address);
      await expect(tx)
        .to.emit(roles, "GrantRole")
        .withArgs(ROLE_KEY_2, member.address, 0, maxUint64, maxUint128);
    });
  });

  describe("setDefaultRole", () => {
    it("sets default role for module", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.setDefaultRole(member.address, ROLE_KEY);

      expect(await roles.defaultRoles(member.address)).to.equal(ROLE_KEY);
    });

    it("emits SetDefaultRole event", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await expect(roles.setDefaultRole(member.address, ROLE_KEY))
        .to.emit(roles, "SetDefaultRole")
        .withArgs(member.address, ROLE_KEY);
    });

    it("allows setting to zero role (effectively no default)", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.setDefaultRole(member.address, ROLE_KEY);

      await expect(roles.setDefaultRole(member.address, ZeroHash))
        .to.emit(roles, "SetDefaultRole")
        .withArgs(member.address, ZeroHash);

      expect(await roles.defaultRoles(member.address)).to.equal(ZeroHash);
    });

    it("overwrites existing default role", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const ROLE_KEY_2 = ethers.id("TEST_ROLE_2");

      await roles.setDefaultRole(member.address, ROLE_KEY);
      expect(await roles.defaultRoles(member.address)).to.equal(ROLE_KEY);

      await roles.setDefaultRole(member.address, ROLE_KEY_2);
      expect(await roles.defaultRoles(member.address)).to.equal(ROLE_KEY_2);
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // TARGET PERMISSIONS
  // ═══════════════════════════════════════════════════════════════════════════

  describe("allowTarget", () => {
    it("sets clearance to Target for address", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");

      await roles.allowTargetPacked(
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      // Can call any function on target
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.not.be.revert(ethers);
    });

    it("validates condition tree integrity on pack", async () => {
      const { roles, evaluator } = await loadFixture(setup);

      // Invalid: root node has invalid parent reference (must be 0 for root)
      await expect(
        roles.packConditions([
          {
            parent: 5, // Invalid - root node must have parent 0
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithCustomError(evaluator, "UnsuitableRootNode");
    });

    it("emits AllowTarget event", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      await expect(
        roles.allowTargetPacked(
          ROLE_KEY,
          testContractAddress,
          "0x",
          ExecutionOptions.None,
        ),
      )
        .to.emit(roles, "AllowTarget")
        .withArgs(ROLE_KEY, testContractAddress, "0x", ExecutionOptions.None);
    });

    it("overwrites existing target permission", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);

      // Allow target with no conditions
      await roles.allowTargetPacked(
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      // Any param value works
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [99]),
            0,
          ),
      ).to.not.be.revert(ethers);

      // Overwrite with condition: param must equal 42
      const conditionsEq42 = await packConditions(roles, [
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.EqualTo,
          compValue: ethers.AbiCoder.defaultAbiCoder().encode(
            ["uint256"],
            [42],
          ),
        },
      ]);
      await roles.allowTargetPacked(
        ROLE_KEY,
        testContractAddress,
        conditionsEq42,
        ExecutionOptions.None,
      );

      // Now 99 should fail
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [99]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "ConditionViolation");

      // But 42 should pass
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [42]),
            0,
          ),
      ).to.not.be.revert(ethers);
    });

    it("reverts with ZeroAddressNotAllowed for address(0)", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);

      await expect(
        roles.allowTargetPacked(
          ROLE_KEY,
          ZeroAddress,
          "0x",
          ExecutionOptions.None,
        ),
      ).to.be.revertedWithCustomError(roles, "ZeroAddressNotAllowed");

      await expect(
        roles.allowTarget(ROLE_KEY, ZeroAddress, [], ExecutionOptions.None),
      ).to.be.revertedWithCustomError(roles, "ZeroAddressNotAllowed");
    });
  });

  describe("scopeTarget", () => {
    it("sets clearance to Function for address", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.scopeTarget(ROLE_KEY, testContractAddress);

      // Without allowFunction, calls should fail
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
    });

    it("emits ScopeTarget event", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      await expect(roles.scopeTarget(ROLE_KEY, testContractAddress))
        .to.emit(roles, "ScopeTarget")
        .withArgs(ROLE_KEY, testContractAddress);
    });

    it("reverts with ZeroAddressNotAllowed for address(0)", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);

      await expect(
        roles.scopeTarget(ROLE_KEY, ZeroAddress),
      ).to.be.revertedWithCustomError(roles, "ZeroAddressNotAllowed");
    });
  });

  describe("revokeTarget", () => {
    it("sets clearance to None for address", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.allowTargetPacked(
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      // Verify target is allowed before revoking
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.not.be.revert(ethers);

      await roles.revokeTarget(ROLE_KEY, testContractAddress);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");
    });

    it("emits RevokeTarget event", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      await roles.allowTargetPacked(
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      await expect(roles.revokeTarget(ROLE_KEY, testContractAddress))
        .to.emit(roles, "RevokeTarget")
        .withArgs(ROLE_KEY, testContractAddress);
    });

    it("does not clear function-level scopeConfig entries", async () => {
      const { roles, member, testContract, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = iface.getFunction("doNothing")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.scopeTarget(ROLE_KEY, testContractAddress);
      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector,
        "0x",
        ExecutionOptions.None,
      );

      // Revoke - target no longer allowed
      await roles.revokeTarget(ROLE_KEY, testContractAddress);

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

      // Re-scope - function should still be allowed (scopeConfig preserved)
      await roles.scopeTarget(ROLE_KEY, testContractAddress);

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
        .to.emit(testContract, "Invoked")
        .withArgs(selector);
    });

    it("succeeds even if target was not allowed", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      await expect(
        roles.revokeTarget(ROLE_KEY, testContractAddress),
      ).to.not.be.revert(ethers);
    });

    it("reverts with ZeroAddressNotAllowed for address(0)", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);

      await expect(
        roles.revokeTarget(ROLE_KEY, ZeroAddress),
      ).to.be.revertedWithCustomError(roles, "ZeroAddressNotAllowed");
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // FUNCTION PERMISSIONS
  // ═══════════════════════════════════════════════════════════════════════════

  describe("allowFunction", () => {
    it("stores empty conditions as single Pass node", async () => {
      const { roles, member, testContract, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = iface.getFunction("doNothing")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.scopeTarget(ROLE_KEY, testContractAddress);
      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector,
        "0x",
        ExecutionOptions.None,
      );

      // Should be able to call the function
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
        .to.emit(testContract, "Invoked")
        .withArgs(selector);
    });

    it("stores and enforces provided conditions", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = iface.getFunction("oneParamStatic")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.scopeTarget(ROLE_KEY, testContractAddress);

      // Allow with condition: param must equal 42
      const conditionsEq42 = await packConditions(roles, [
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.EqualTo,
          compValue: ethers.AbiCoder.defaultAbiCoder().encode(
            ["uint256"],
            [42],
          ),
        },
      ]);
      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector,
        conditionsEq42,
        ExecutionOptions.None,
      );

      // Call with 42 - should succeed
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [42]),
            0,
          ),
      ).to.not.be.revert(ethers);

      // Call with 99 - should fail
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [99]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "ConditionViolation");
    });

    it("validates condition tree integrity on pack", async () => {
      const { roles, evaluator } = await loadFixture(setup);

      // Invalid: root node has invalid parent reference (must be 0 for root)
      await expect(
        roles.packConditions([
          {
            parent: 5, // Invalid - root node must have parent 0
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithCustomError(evaluator, "UnsuitableRootNode");
    });

    it("emits AllowFunction event", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      const selector = iface.getFunction("doNothing")!.selector;

      await expect(
        roles.allowFunctionPacked(
          ROLE_KEY,
          testContractAddress,
          selector,
          "0x",
          ExecutionOptions.None,
        ),
      )
        .to.emit(roles, "AllowFunction")
        .withArgs(
          ROLE_KEY,
          testContractAddress,
          selector,
          "0x",
          ExecutionOptions.None,
        );
    });

    it("overwrites existing function permission", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = iface.getFunction("oneParamStatic")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.scopeTarget(ROLE_KEY, testContractAddress);

      // Allow with condition: param must equal 1
      const conditionsEq1 = await packConditions(roles, [
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.EqualTo,
          compValue: ethers.AbiCoder.defaultAbiCoder().encode(["uint256"], [1]),
        },
      ]);
      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector,
        conditionsEq1,
        ExecutionOptions.None,
      );

      // Call with 2 should fail
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [2]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "ConditionViolation");

      // Overwrite: param must equal 2
      const conditionsEq2 = await packConditions(roles, [
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.EqualTo,
          compValue: ethers.AbiCoder.defaultAbiCoder().encode(["uint256"], [2]),
        },
      ]);
      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector,
        conditionsEq2,
        ExecutionOptions.None,
      );

      // Call with 2 should now pass
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [2]),
            0,
          ),
      ).to.not.be.revert(ethers);
    });

    it("reverts with ZeroAddressNotAllowed for address(0)", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);
      const selector = iface.getFunction("doNothing")!.selector;

      await expect(
        roles.allowFunctionPacked(
          ROLE_KEY,
          ZeroAddress,
          selector,
          "0x",
          ExecutionOptions.None,
        ),
      ).to.be.revertedWithCustomError(roles, "ZeroAddressNotAllowed");

      await expect(
        roles.allowFunction(
          ROLE_KEY,
          ZeroAddress,
          selector,
          [],
          ExecutionOptions.None,
        ),
      ).to.be.revertedWithCustomError(roles, "ZeroAddressNotAllowed");
    });
  });

  describe("revokeFunction", () => {
    it("deletes scopeConfig for target + selector", async () => {
      const { roles, member, ROLE_KEY, testContractAddress, testContract } =
        await loadFixture(setup);

      const selector = iface.getFunction("doNothing")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.scopeTarget(ROLE_KEY, testContractAddress);
      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector,
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
      )
        .to.emit(testContract, "Invoked")
        .withArgs(selector);

      await roles.revokeFunction(ROLE_KEY, testContractAddress, selector);

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
    });

    it("emits RevokeFunction event", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      const selector = iface.getFunction("doNothing")!.selector;

      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector,
        "0x",
        ExecutionOptions.None,
      );

      await expect(
        roles.revokeFunction(ROLE_KEY, testContractAddress, selector),
      )
        .to.emit(roles, "RevokeFunction")
        .withArgs(ROLE_KEY, testContractAddress, selector);
    });

    it("does not affect other functions on same target", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector1 = iface.getFunction("doNothing")!.selector;
      const selector2 = iface.getFunction("doEvenLess")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.scopeTarget(ROLE_KEY, testContractAddress);
      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector1,
        "0x",
        ExecutionOptions.None,
      );
      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector2,
        "0x",
        ExecutionOptions.None,
      );

      // Revoke selector1
      await roles.revokeFunction(ROLE_KEY, testContractAddress, selector1);

      // selector1 should be revoked
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

      // selector2 should still be allowed
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doEvenLess"),
            0,
          ),
      ).to.not.be.revert(ethers);
    });

    it("reverts with ZeroAddressNotAllowed for address(0)", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);
      const selector = iface.getFunction("doNothing")!.selector;

      await expect(
        roles.revokeFunction(ROLE_KEY, ZeroAddress, selector),
      ).to.be.revertedWithCustomError(roles, "ZeroAddressNotAllowed");
    });
  });

  describe("allowFunctionGlobally", () => {
    it("stores empty conditions as pass-through", async () => {
      const { roles, member, testContract, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = iface.getFunction("doNothing")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.allowFunctionGlobally(ROLE_KEY, selector, []);

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
        .to.emit(testContract, "Invoked")
        .withArgs(selector);
    });

    it("validates condition tree integrity on pack", async () => {
      const { roles, evaluator, ROLE_KEY } = await loadFixture(setup);
      const selector = iface.getFunction("doNothing")!.selector;

      await expect(
        roles.allowFunctionGlobally(ROLE_KEY, selector, [
          {
            parent: 5, // Invalid - root node must have parent 0
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithCustomError(evaluator, "UnsuitableRootNode");
    });

    it("emits AllowFunctionGlobally event", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);
      const selector = iface.getFunction("doNothing")!.selector;

      await expect(roles.allowFunctionGloballyPacked(ROLE_KEY, selector, "0x"))
        .to.emit(roles, "AllowFunctionGlobally")
        .withArgs(ROLE_KEY, selector, "0x");
    });

    it("overwrites existing global function permission", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = iface.getFunction("oneParamStatic")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);

      const conditionsEq1 = await packConditions(roles, [
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.EqualTo,
          compValue: ethers.AbiCoder.defaultAbiCoder().encode(["uint256"], [1]),
        },
      ]);
      await roles.allowFunctionGloballyPacked(
        ROLE_KEY,
        selector,
        conditionsEq1,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [2]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "ConditionViolation");

      const conditionsEq2 = await packConditions(roles, [
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.EqualTo,
          compValue: ethers.AbiCoder.defaultAbiCoder().encode(["uint256"], [2]),
        },
      ]);
      await roles.allowFunctionGloballyPacked(
        ROLE_KEY,
        selector,
        conditionsEq2,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [2]),
            0,
          ),
      ).to.not.be.revert(ethers);
    });
  });

  describe("revokeFunctionGlobally", () => {
    it("deletes global scopeConfig for selector", async () => {
      const { roles, member, testContract, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = iface.getFunction("doNothing")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.allowFunctionGloballyPacked(ROLE_KEY, selector, "0x");

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
        .to.emit(testContract, "Invoked")
        .withArgs(selector);

      await roles.revokeFunctionGlobally(ROLE_KEY, selector);

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
    });

    it("emits RevokeFunctionGlobally event", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);
      const selector = iface.getFunction("doNothing")!.selector;

      await roles.allowFunctionGloballyPacked(ROLE_KEY, selector, "0x");

      await expect(roles.revokeFunctionGlobally(ROLE_KEY, selector))
        .to.emit(roles, "RevokeFunctionGlobally")
        .withArgs(ROLE_KEY, selector);
    });

    it("does not affect other global selectors", async () => {
      const { roles, member, testContract, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector1 = iface.getFunction("doNothing")!.selector;
      const selector2 = iface.getFunction("doEvenLess")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.allowFunctionGloballyPacked(ROLE_KEY, selector1, "0x");
      await roles.allowFunctionGloballyPacked(ROLE_KEY, selector2, "0x");

      await roles.revokeFunctionGlobally(ROLE_KEY, selector1);

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

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doEvenLess"),
            0,
          ),
      )
        .to.emit(testContract, "Invoked")
        .withArgs(selector2);
    });

    it("succeeds even if global function was not allowed", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);
      const selector = iface.getFunction("doNothing")!.selector;

      await expect(
        roles.revokeFunctionGlobally(ROLE_KEY, selector),
      ).to.not.be.revert(ethers);
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // ALLOWANCES
  // ═══════════════════════════════════════════════════════════════════════════

  describe("setAllowance", () => {
    it("sets balance to specified value", async () => {
      const { roles } = await loadFixture(setup);

      const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

      await roles.setAllowance(ALLOWANCE_KEY, 500, 1000, 100, 3600, 0);

      const allowance = await roles.allowances(ALLOWANCE_KEY);
      expect(allowance.balance).to.equal(500);
    });

    it("sets refill to specified value", async () => {
      const { roles } = await loadFixture(setup);

      const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

      await roles.setAllowance(ALLOWANCE_KEY, 500, 1000, 100, 3600, 0);

      const allowance = await roles.allowances(ALLOWANCE_KEY);
      expect(allowance.refill).to.equal(100);
    });

    it("sets period to specified value", async () => {
      const { roles } = await loadFixture(setup);

      const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

      await roles.setAllowance(ALLOWANCE_KEY, 500, 1000, 100, 3600, 0);

      const allowance = await roles.allowances(ALLOWANCE_KEY);
      expect(allowance.period).to.equal(3600);
    });

    it("emits SetAllowance with the stored values, defaults resolved", async () => {
      const { roles } = await loadFixture(setup);

      const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

      const tx = await roles.setAllowance(ALLOWANCE_KEY, 500, 0, 100, 3600, 0);
      const block = await ethers.provider.getBlock(
        (await tx.wait())!.blockNumber,
      );

      await expect(tx)
        .to.emit(roles, "SetAllowance")
        .withArgs(ALLOWANCE_KEY, 500, maxUint128, 100, 3600, block!.timestamp);
    });

    describe("default values", () => {
      it("sets maxRefill to max uint128 when passed 0", async () => {
        const { roles } = await loadFixture(setup);

        const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

        await roles.setAllowance(ALLOWANCE_KEY, 500, 0, 100, 3600, 0);

        const allowance = await roles.allowances(ALLOWANCE_KEY);
        expect(allowance.maxRefill).to.equal(maxUint128);
      });

      it("sets timestamp to current block.timestamp when passed 0", async () => {
        const { roles } = await loadFixture(setup);

        const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

        const tx = await roles.setAllowance(
          ALLOWANCE_KEY,
          500,
          1000,
          100,
          3600,
          0,
        );

        const receipt = await tx.wait();
        const block = await ethers.provider.getBlock(receipt!.blockNumber);

        const allowance = await roles.allowances(ALLOWANCE_KEY);
        expect(allowance.timestamp).to.equal(block!.timestamp);
      });
    });

    it("overwrites all fields of existing allowance", async () => {
      const { roles } = await loadFixture(setup);

      const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

      await roles.setAllowance(ALLOWANCE_KEY, 500, 1000, 100, 3600, 0);
      await time.increase(1000);
      const tx = await roles.setAllowance(
        ALLOWANCE_KEY,
        999,
        2000,
        200,
        7200,
        0,
      );
      const block = await ethers.provider.getBlock(
        (await tx.wait())!.blockNumber,
      );

      const allowance = await roles.allowances(ALLOWANCE_KEY);
      expect(allowance.balance).to.equal(999);
      expect(allowance.maxRefill).to.equal(2000);
      expect(allowance.refill).to.equal(200);
      expect(allowance.period).to.equal(7200);
      expect(allowance.timestamp).to.equal(block!.timestamp);
    });
  });

  describe("updateAllowance", () => {
    it("updates refill parameters only", async () => {
      const { roles } = await loadFixture(setup);

      const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

      await roles.setAllowance(ALLOWANCE_KEY, 500, 1000, 100, 3600, 0);
      await roles.updateAllowance(ALLOWANCE_KEY, 2000, 200, 7200);

      const allowance = await roles.allowances(ALLOWANCE_KEY);
      expect(allowance.maxRefill).to.equal(2000);
      expect(allowance.refill).to.equal(200);
      expect(allowance.period).to.equal(7200);
    });

    it("preserves existing balance", async () => {
      const { roles } = await loadFixture(setup);

      const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

      await roles.setAllowance(ALLOWANCE_KEY, 500, 1000, 100, 3600, 0);
      await roles.updateAllowance(ALLOWANCE_KEY, 2000, 200, 7200);

      const allowance = await roles.allowances(ALLOWANCE_KEY);
      expect(allowance.balance).to.equal(500);
    });

    it("preserves existing timestamp", async () => {
      const { roles } = await loadFixture(setup);

      const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

      await roles.setAllowance(ALLOWANCE_KEY, 500, 1000, 100, 3600, 0);

      const initialAllowance = await roles.allowances(ALLOWANCE_KEY);

      await time.increase(1000);

      await roles.updateAllowance(ALLOWANCE_KEY, 2000, 200, 7200);

      const allowance = await roles.allowances(ALLOWANCE_KEY);
      expect(allowance.timestamp).to.equal(initialAllowance.timestamp);
    });

    it("emits SetAllowance with the preserved balance and timestamp", async () => {
      const { roles } = await loadFixture(setup);

      const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

      await roles.setAllowance(ALLOWANCE_KEY, 500, 1000, 100, 3600, 0);
      const { timestamp } = await roles.allowances(ALLOWANCE_KEY);
      await time.increase(1000);

      await expect(roles.updateAllowance(ALLOWANCE_KEY, 0, 200, 7200))
        .to.emit(roles, "SetAllowance")
        .withArgs(ALLOWANCE_KEY, 500, maxUint128, 200, 7200, timestamp);
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // ADAPTERS
  // ═══════════════════════════════════════════════════════════════════════════

  describe("setTransactionUnwrapper", () => {
    it("registers unwrapper for target + selector", async () => {
      const { roles, testContractAddress } = await loadFixture(setup);

      const MultiSendUnwrapper =
        await ethers.getContractFactory("MultiSendUnwrapper");
      const unwrapper = await MultiSendUnwrapper.deploy();
      const unwrapperAddress = await unwrapper.getAddress();

      const selector = iface.getFunction("doNothing")!.selector;

      await expect(
        roles.setTransactionUnwrapper(
          testContractAddress,
          selector,
          unwrapperAddress,
        ),
      )
        .to.emit(roles, "SetUnwrapAdapter")
        .withArgs(testContractAddress, selector, unwrapperAddress);
    });

    it("emits SetUnwrapAdapter event", async () => {
      const { roles, testContractAddress } = await loadFixture(setup);

      const MultiSendUnwrapper =
        await ethers.getContractFactory("MultiSendUnwrapper");
      const unwrapper = await MultiSendUnwrapper.deploy();
      const unwrapperAddress = await unwrapper.getAddress();

      const selector = iface.getFunction("doNothing")!.selector;

      await expect(
        roles.setTransactionUnwrapper(
          testContractAddress,
          selector,
          unwrapperAddress,
        ),
      )
        .to.emit(roles, "SetUnwrapAdapter")
        .withArgs(testContractAddress, selector, unwrapperAddress);
    });

    it("can update existing unwrapper", async () => {
      const { roles, testContractAddress } = await loadFixture(setup);

      const MultiSendUnwrapper =
        await ethers.getContractFactory("MultiSendUnwrapper");
      const unwrapper1 = await MultiSendUnwrapper.deploy();
      const unwrapper2 = await MultiSendUnwrapper.deploy();
      const unwrapper2Address = await unwrapper2.getAddress();

      const selector = iface.getFunction("doNothing")!.selector;

      await roles.setTransactionUnwrapper(
        testContractAddress,
        selector,
        await unwrapper1.getAddress(),
      );

      // Second call updates to unwrapper2
      await expect(
        roles.setTransactionUnwrapper(
          testContractAddress,
          selector,
          unwrapper2Address,
        ),
      )
        .to.emit(roles, "SetUnwrapAdapter")
        .withArgs(testContractAddress, selector, unwrapper2Address);
    });

    it("can remove unwrapper by setting to zero address", async () => {
      const { roles, testContractAddress } = await loadFixture(setup);

      const MultiSendUnwrapper =
        await ethers.getContractFactory("MultiSendUnwrapper");
      const unwrapper = await MultiSendUnwrapper.deploy();
      const unwrapperAddress = await unwrapper.getAddress();

      const selector = iface.getFunction("doNothing")!.selector;

      await roles.setTransactionUnwrapper(
        testContractAddress,
        selector,
        unwrapperAddress,
      );

      await expect(
        roles.setTransactionUnwrapper(
          testContractAddress,
          selector,
          ZeroAddress,
        ),
      )
        .to.emit(roles, "SetUnwrapAdapter")
        .withArgs(testContractAddress, selector, ZeroAddress);
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // ISOLATION
  // ═══════════════════════════════════════════════════════════════════════════

  describe("Isolation", () => {
    it("allowing one target does not allow another target", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const TestContract2 = await ethers.getContractFactory("TestContract");
      const testContract2 = await TestContract2.deploy();
      const testContract2Address = await testContract2.getAddress();

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.allowTargetPacked(
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      // testContractAddress is allowed
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.not.be.revert(ethers);

      // testContract2Address is NOT allowed
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContract2Address, 0, "0x", 0),
      ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");
    });

    it("allowing one function does not allow other functions on same target", async () => {
      const { roles, member, ROLE_KEY, testContractAddress, testContract } =
        await loadFixture(setup);

      const selector1 = iface.getFunction("doNothing")!.selector;
      const selector2 = iface.getFunction("other")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.scopeTarget(ROLE_KEY, testContractAddress);
      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector1,
        "0x",
        ExecutionOptions.None,
      );

      // selector1 is allowed
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
        .to.emit(testContract, "Invoked")
        .withArgs(selector1);

      // selector2 is NOT allowed
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("other"),
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");
    });

    it("allowing a function on one target does not allow it on another target", async () => {
      const { roles, member, ROLE_KEY, testContractAddress, testContract } =
        await loadFixture(setup);

      const TestContract2 = await ethers.getContractFactory("TestContract");
      const testContract2 = await TestContract2.deploy();
      const testContract2Address = await testContract2.getAddress();

      const selector = iface.getFunction("doNothing")!.selector;

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.scopeTarget(ROLE_KEY, testContractAddress);
      await roles.scopeTarget(ROLE_KEY, testContract2Address);
      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector,
        "0x",
        ExecutionOptions.None,
      );

      // Function on testContractAddress is allowed
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
        .to.emit(testContract, "Invoked")
        .withArgs(selector);

      // Same function on testContract2Address is NOT allowed
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContract2Address,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");
    });

    it("multiple roles can have different permissions on same target", async () => {
      const { roles, member, ROLE_KEY, testContractAddress, testContract } =
        await loadFixture(setup);

      const ROLE_KEY_2 = ethers.id("TEST_ROLE_2");

      const selector1 = iface.getFunction("doNothing")!.selector;
      const selector2 = iface.getFunction("doEvenLess")!.selector;

      // Setup: member has ROLE_KEY, grant them both roles
      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.grantRole(member.address, ROLE_KEY_2, 0, 0, 0);

      // ROLE_KEY: only selector1 allowed
      await roles.scopeTarget(ROLE_KEY, testContractAddress);
      await roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        selector1,
        "0x",
        ExecutionOptions.None,
      );

      // ROLE_KEY_2: only selector2 allowed
      await roles.scopeTarget(ROLE_KEY_2, testContractAddress);
      await roles.allowFunctionPacked(
        ROLE_KEY_2,
        testContractAddress,
        selector2,
        "0x",
        ExecutionOptions.None,
      );

      // With ROLE_KEY as default, can call selector1 but not selector2
      await roles.setDefaultRole(member.address, ROLE_KEY);

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
        .to.emit(testContract, "Invoked")
        .withArgs(selector1);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doEvenLess"),
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");

      // With ROLE_KEY_2 as default, can call selector2 but not selector1
      await roles.setDefaultRole(member.address, ROLE_KEY_2);

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

      // selector2 is now allowed
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doEvenLess"),
            0,
          ),
      ).to.not.be.revert(ethers);
    });
  });
});
