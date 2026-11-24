import assert from "node:assert/strict";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import {
  encodeAbiParameters,
  encodeFunctionData,
  keccak256,
  parseAbi,
  parseAbiParameters,
  toBytes,
  toFunctionSelector,
  zeroAddress,
  zeroHash,
} from "viem";
import type { Hex } from "viem";

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
const { viem, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { deployEvaluator, deployRolesMod } = createSetup(connection);

const abi = parseAbi([
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
    const [owner, member] = await viem.getWalletClients();

    const avatar = await viem.deployContract("TestAvatar");
    const avatarAddress = avatar.address;

    const evaluator = await deployEvaluator();
    const roles = await deployRolesMod(
      owner.account.address,
      avatarAddress,
      avatarAddress,
      evaluator.address,
    );

    const testContract = await viem.deployContract("TestContract");
    const testContractAddress = testContract.address;

    const ROLE_KEY = keccak256(toBytes("TEST_ROLE"));

    const storedAllowance = async (key: Hex) => {
      const [refill, maxRefill, period, balance, timestamp] =
        await roles.read.allowances([key]);
      return { refill, maxRefill, period, balance, timestamp };
    };

    return {
      roles,
      evaluator,
      owner,
      member,
      testContract,
      testContractAddress,
      ROLE_KEY,
      storedAllowance,
    };
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // ROLE MEMBERSHIP
  // ═══════════════════════════════════════════════════════════════════════════

  describe("grantRole", () => {
    it("grants role to module", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      // Member can now execute - proves role was granted
      await roles.write.execTransactionFromModule(
        [testContractAddress, 0n, "0x", 0],
        { account: member.account },
      );
    });

    it("automatically enables module if not already enabled", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      assert.equal(
        await roles.read.isModuleEnabled([member.account.address]),
        false,
      );

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);

      assert.equal(
        await roles.read.isModuleEnabled([member.account.address]),
        true,
      );
    });

    it("emits GrantRole event", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await viem.assertions.emitWithArgs(
        roles.write.grantRole([
          member.account.address,
          ROLE_KEY,
          100n,
          200n,
          5n,
        ]),
        roles,
        "GrantRole",
        [ROLE_KEY, member.account.address, 100n, 200n, 5n],
      );
    });

    describe("validity window", () => {
      it("sets start timestamp when start > 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await viem.assertions.emitWithArgs(
          roles.write.grantRole([
            member.account.address,
            ROLE_KEY,
            1000n,
            0n,
            0n,
          ]),
          roles,
          "GrantRole",
          [ROLE_KEY, member.account.address, 1000n, maxUint64, maxUint128],
        );
      });

      it("defaults to immediately valid when start = 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await viem.assertions.emitWithArgs(
          roles.write.grantRole([member.account.address, ROLE_KEY, 0n, 0n, 0n]),
          roles,
          "GrantRole",
          [ROLE_KEY, member.account.address, 0n, maxUint64, maxUint128],
        );
      });

      it("sets end timestamp when end > 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await viem.assertions.emitWithArgs(
          roles.write.grantRole([
            member.account.address,
            ROLE_KEY,
            0n,
            9999n,
            0n,
          ]),
          roles,
          "GrantRole",
          [ROLE_KEY, member.account.address, 0n, 9999n, maxUint128],
        );
      });

      it("defaults to never expires (max uint64) when end = 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await viem.assertions.emitWithArgs(
          roles.write.grantRole([member.account.address, ROLE_KEY, 0n, 0n, 0n]),
          roles,
          "GrantRole",
          [ROLE_KEY, member.account.address, 0n, maxUint64, maxUint128],
        );
      });
    });

    describe("usage limits", () => {
      it("sets finite usesLeft when usesLeft > 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await viem.assertions.emitWithArgs(
          roles.write.grantRole([
            member.account.address,
            ROLE_KEY,
            0n,
            0n,
            10n,
          ]),
          roles,
          "GrantRole",
          [ROLE_KEY, member.account.address, 0n, maxUint64, 10n],
        );
      });

      it("defaults to unlimited uses (max uint128) when usesLeft = 0", async () => {
        const { roles, member, ROLE_KEY } = await loadFixture(setup);

        await viem.assertions.emitWithArgs(
          roles.write.grantRole([member.account.address, ROLE_KEY, 0n, 0n, 0n]),
          roles,
          "GrantRole",
          [ROLE_KEY, member.account.address, 0n, maxUint64, maxUint128],
        );
      });
    });

    it("overwrites existing membership with new parameters", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        100n,
        200n,
        5n,
      ]);

      await viem.assertions.emitWithArgs(
        roles.write.grantRole([
          member.account.address,
          ROLE_KEY,
          300n,
          400n,
          10n,
        ]),
        roles,
        "GrantRole",
        [ROLE_KEY, member.account.address, 300n, 400n, 10n],
      );
    });
  });

  describe("revokeRole", () => {
    it("removes membership from role", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      await roles.write.execTransactionFromModule(
        [testContractAddress, 0n, "0x", 0],
        { account: member.account },
      );

      await roles.write.revokeRole([member.account.address, ROLE_KEY]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x", 0],
          { account: member.account },
        ),
        roles,
        "NoMembership",
      );
    });

    it("emits RevokeRole event", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);

      await viem.assertions.emitWithArgs(
        roles.write.revokeRole([member.account.address, ROLE_KEY]),
        roles,
        "RevokeRole",
        [ROLE_KEY, member.account.address],
      );
    });

    it("does not disable module (may have other roles)", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const ROLE_KEY_2 = keccak256(toBytes("TEST_ROLE_2"));

      assert.equal(
        await roles.read.isModuleEnabled([member.account.address]),
        false,
      );
      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY_2,
        0n,
        0n,
        0n,
      ]);
      await roles.write.revokeRole([member.account.address, ROLE_KEY]);
      assert.equal(
        await roles.read.isModuleEnabled([member.account.address]),
        true,
      );
    });

    it("succeeds even if membership doesn't exist", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.write.revokeRole([member.account.address, ROLE_KEY]);
    });
  });

  describe("renounceRole", () => {
    it("allows member to revoke their own role", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      await roles.write.execTransactionFromModule(
        [testContractAddress, 0n, "0x", 0],
        { account: member.account },
      );

      await roles.write.renounceRole([ROLE_KEY], { account: member.account });

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x", 0],
          { account: member.account },
        ),
        roles,
        "NoMembership",
      );
    });

    it("emits RevokeRole event", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);

      await viem.assertions.emitWithArgs(
        roles.write.renounceRole([ROLE_KEY], { account: member.account }),
        roles,
        "RevokeRole",
        [ROLE_KEY, member.account.address],
      );
    });
  });

  describe("assignRoles", () => {
    it("batch grants roles when memberOf is true", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const ROLE_KEY_2 = keccak256(toBytes("TEST_ROLE_2"));

      await roles.write.assignRoles([
        member.account.address,
        [ROLE_KEY, ROLE_KEY_2],
        [true, true],
      ]);

      assert.equal(
        await roles.read.isModuleEnabled([member.account.address]),
        true,
      );
    });

    it("batch revokes roles when memberOf is false", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const ROLE_KEY_2 = keccak256(toBytes("TEST_ROLE_2"));

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY_2,
        0n,
        0n,
        0n,
      ]);

      await viem.assertions.emitWithArgs(
        roles.write.assignRoles([
          member.account.address,
          [ROLE_KEY, ROLE_KEY_2],
          [false, false],
        ]),
        roles,
        "RevokeRole",
        [ROLE_KEY, member.account.address],
      );
    });

    it("handles mixed grant and revoke in single call", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const ROLE_KEY_2 = keccak256(toBytes("TEST_ROLE_2"));

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);

      // Revoke ROLE_KEY, grant ROLE_KEY_2
      const hash = await roles.write.assignRoles([
        member.account.address,
        [ROLE_KEY, ROLE_KEY_2],
        [false, true],
      ]);

      await viem.assertions.emitWithArgs(hash, roles, "RevokeRole", [
        ROLE_KEY,
        member.account.address,
      ]);
      await viem.assertions.emitWithArgs(hash, roles, "GrantRole", [
        ROLE_KEY_2,
        member.account.address,
        0n,
        maxUint64,
        maxUint128,
      ]);
    });
  });

  describe("setDefaultRole", () => {
    it("sets default role for module", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);

      assert.equal(
        await roles.read.defaultRoles([member.account.address]),
        ROLE_KEY,
      );
    });

    it("emits SetDefaultRole event", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await viem.assertions.emitWithArgs(
        roles.write.setDefaultRole([member.account.address, ROLE_KEY]),
        roles,
        "SetDefaultRole",
        [member.account.address, ROLE_KEY],
      );
    });

    it("allows setting to zero role (effectively no default)", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);

      await viem.assertions.emitWithArgs(
        roles.write.setDefaultRole([member.account.address, zeroHash]),
        roles,
        "SetDefaultRole",
        [member.account.address, zeroHash],
      );

      assert.equal(
        await roles.read.defaultRoles([member.account.address]),
        zeroHash,
      );
    });

    it("overwrites existing default role", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const ROLE_KEY_2 = keccak256(toBytes("TEST_ROLE_2"));

      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      assert.equal(
        await roles.read.defaultRoles([member.account.address]),
        ROLE_KEY,
      );

      await roles.write.setDefaultRole([member.account.address, ROLE_KEY_2]);
      assert.equal(
        await roles.read.defaultRoles([member.account.address]),
        ROLE_KEY_2,
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // TARGET PERMISSIONS
  // ═══════════════════════════════════════════════════════════════════════════

  describe("allowTarget", () => {
    it("sets clearance to Target for address", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x", 0],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );

      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      // Can call any function on target
      await roles.write.execTransactionFromModule(
        [testContractAddress, 0n, "0x", 0],
        { account: member.account },
      );
    });

    it("validates condition tree integrity on pack", async () => {
      const { roles, evaluator } = await loadFixture(setup);

      // Invalid: root node has invalid parent reference (must be 0 for root)
      await viem.assertions.revertWithCustomError(
        roles.read.packConditions([
          [
            {
              parent: 5, // Invalid - root node must have parent 0
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            },
          ],
        ]),
        evaluator,
        "UnsuitableRootNode",
      );
    });

    it("emits AllowTarget event", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      await viem.assertions.emitWithArgs(
        roles.write.allowTargetPacked([
          ROLE_KEY,
          testContractAddress,
          "0x",
          ExecutionOptions.None,
        ]),
        roles,
        "AllowTarget",
        [ROLE_KEY, testContractAddress, "0x", ExecutionOptions.None],
      );
    });

    it("overwrites existing target permission", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);

      // Allow target with no conditions
      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      // Any param value works
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [99n],
          }),
          0,
        ],
        { account: member.account },
      );

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
          compValue: encodeAbiParameters(parseAbiParameters("uint256"), [42n]),
        },
      ]);
      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        conditionsEq42,
        ExecutionOptions.None,
      ]);

      // Now 99 should fail
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [99n],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
      );

      // But 42 should pass
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [42n],
          }),
          0,
        ],
        { account: member.account },
      );
    });

    it("reverts with ZeroAddressNotAllowed for address(0)", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);

      await viem.assertions.revertWithCustomError(
        roles.write.allowTargetPacked([
          ROLE_KEY,
          zeroAddress,
          "0x",
          ExecutionOptions.None,
        ]),
        roles,
        "ZeroAddressNotAllowed",
      );

      await viem.assertions.revertWithCustomError(
        roles.write.allowTarget([
          ROLE_KEY,
          zeroAddress,
          [],
          ExecutionOptions.None,
        ]),
        roles,
        "ZeroAddressNotAllowed",
      );
    });
  });

  describe("scopeTarget", () => {
    it("sets clearance to Function for address", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);

      // Without allowFunction, calls should fail
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );
    });

    it("emits ScopeTarget event", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      await viem.assertions.emitWithArgs(
        roles.write.scopeTarget([ROLE_KEY, testContractAddress]),
        roles,
        "ScopeTarget",
        [ROLE_KEY, testContractAddress],
      );
    });

    it("reverts with ZeroAddressNotAllowed for address(0)", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);

      await viem.assertions.revertWithCustomError(
        roles.write.scopeTarget([ROLE_KEY, zeroAddress]),
        roles,
        "ZeroAddressNotAllowed",
      );
    });
  });

  describe("revokeTarget", () => {
    it("sets clearance to None for address", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      // Verify target is allowed before revoking
      await roles.write.execTransactionFromModule(
        [testContractAddress, 0n, "0x", 0],
        { account: member.account },
      );

      await roles.write.revokeTarget([ROLE_KEY, testContractAddress]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x", 0],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );
    });

    it("emits RevokeTarget event", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      await viem.assertions.emitWithArgs(
        roles.write.revokeTarget([ROLE_KEY, testContractAddress]),
        roles,
        "RevokeTarget",
        [ROLE_KEY, testContractAddress],
      );
    });

    it("does not clear function-level scopeConfig entries", async () => {
      const { roles, member, testContract, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = toFunctionSelector("doNothing()");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector,
        "0x",
        ExecutionOptions.None,
      ]);

      // Revoke - target no longer allowed
      await roles.write.revokeTarget([ROLE_KEY, testContractAddress]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );

      // Re-scope - function should still be allowed (scopeConfig preserved)
      await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);

      await viem.assertions.emitWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        testContract,
        "Invoked",
        [selector],
      );
    });

    it("succeeds even if target was not allowed", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      await roles.write.revokeTarget([ROLE_KEY, testContractAddress]);
    });

    it("reverts with ZeroAddressNotAllowed for address(0)", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);

      await viem.assertions.revertWithCustomError(
        roles.write.revokeTarget([ROLE_KEY, zeroAddress]),
        roles,
        "ZeroAddressNotAllowed",
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // FUNCTION PERMISSIONS
  // ═══════════════════════════════════════════════════════════════════════════

  describe("allowFunction", () => {
    it("stores empty conditions as single Pass node", async () => {
      const { roles, member, testContract, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = toFunctionSelector("doNothing()");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector,
        "0x",
        ExecutionOptions.None,
      ]);

      // Should be able to call the function
      await viem.assertions.emitWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        testContract,
        "Invoked",
        [selector],
      );
    });

    it("stores and enforces provided conditions", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = toFunctionSelector("oneParamStatic(uint256)");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);

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
          compValue: encodeAbiParameters(parseAbiParameters("uint256"), [42n]),
        },
      ]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector,
        conditionsEq42,
        ExecutionOptions.None,
      ]);

      // Call with 42 - should succeed
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [42n],
          }),
          0,
        ],
        { account: member.account },
      );

      // Call with 99 - should fail
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [99n],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
      );
    });

    it("validates condition tree integrity on pack", async () => {
      const { roles, evaluator } = await loadFixture(setup);

      // Invalid: root node has invalid parent reference (must be 0 for root)
      await viem.assertions.revertWithCustomError(
        roles.read.packConditions([
          [
            {
              parent: 5, // Invalid - root node must have parent 0
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            },
          ],
        ]),
        evaluator,
        "UnsuitableRootNode",
      );
    });

    it("emits AllowFunction event", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      const selector = toFunctionSelector("doNothing()");

      await viem.assertions.emitWithArgs(
        roles.write.allowFunctionPacked([
          ROLE_KEY,
          testContractAddress,
          selector,
          "0x",
          ExecutionOptions.None,
        ]),
        roles,
        "AllowFunction",
        [ROLE_KEY, testContractAddress, selector, "0x", ExecutionOptions.None],
      );
    });

    it("overwrites existing function permission", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = toFunctionSelector("oneParamStatic(uint256)");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);

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
          compValue: encodeAbiParameters(parseAbiParameters("uint256"), [1n]),
        },
      ]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector,
        conditionsEq1,
        ExecutionOptions.None,
      ]);

      // Call with 2 should fail
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [2n],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
      );

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
          compValue: encodeAbiParameters(parseAbiParameters("uint256"), [2n]),
        },
      ]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector,
        conditionsEq2,
        ExecutionOptions.None,
      ]);

      // Call with 2 should now pass
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [2n],
          }),
          0,
        ],
        { account: member.account },
      );
    });

    it("reverts with ZeroAddressNotAllowed for address(0)", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);
      const selector = toFunctionSelector("doNothing()");

      await viem.assertions.revertWithCustomError(
        roles.write.allowFunctionPacked([
          ROLE_KEY,
          zeroAddress,
          selector,
          "0x",
          ExecutionOptions.None,
        ]),
        roles,
        "ZeroAddressNotAllowed",
      );

      await viem.assertions.revertWithCustomError(
        roles.write.allowFunction([
          ROLE_KEY,
          zeroAddress,
          selector,
          [],
          ExecutionOptions.None,
        ]),
        roles,
        "ZeroAddressNotAllowed",
      );
    });
  });

  describe("revokeFunction", () => {
    it("deletes scopeConfig for target + selector", async () => {
      const { roles, member, ROLE_KEY, testContractAddress, testContract } =
        await loadFixture(setup);

      const selector = toFunctionSelector("doNothing()");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector,
        "0x",
        ExecutionOptions.None,
      ]);

      await viem.assertions.emitWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        testContract,
        "Invoked",
        [selector],
      );

      await roles.write.revokeFunction([
        ROLE_KEY,
        testContractAddress,
        selector,
      ]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );
    });

    it("emits RevokeFunction event", async () => {
      const { roles, ROLE_KEY, testContractAddress } = await loadFixture(setup);

      const selector = toFunctionSelector("doNothing()");

      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector,
        "0x",
        ExecutionOptions.None,
      ]);

      await viem.assertions.emitWithArgs(
        roles.write.revokeFunction([ROLE_KEY, testContractAddress, selector]),
        roles,
        "RevokeFunction",
        [ROLE_KEY, testContractAddress, selector],
      );
    });

    it("does not affect other functions on same target", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector1 = toFunctionSelector("doNothing()");
      const selector2 = toFunctionSelector("doEvenLess()");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector1,
        "0x",
        ExecutionOptions.None,
      ]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector2,
        "0x",
        ExecutionOptions.None,
      ]);

      // Revoke selector1
      await roles.write.revokeFunction([
        ROLE_KEY,
        testContractAddress,
        selector1,
      ]);

      // selector1 should be revoked
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );

      // selector2 should still be allowed
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({ abi, functionName: "doEvenLess" }),
          0,
        ],
        { account: member.account },
      );
    });

    it("reverts with ZeroAddressNotAllowed for address(0)", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);
      const selector = toFunctionSelector("doNothing()");

      await viem.assertions.revertWithCustomError(
        roles.write.revokeFunction([ROLE_KEY, zeroAddress, selector]),
        roles,
        "ZeroAddressNotAllowed",
      );
    });
  });

  describe("allowFunctionGlobally", () => {
    it("stores empty conditions as pass-through", async () => {
      const { roles, member, testContract, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = toFunctionSelector("doNothing()");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.allowFunctionGlobally([ROLE_KEY, selector, []]);

      await viem.assertions.emitWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        testContract,
        "Invoked",
        [selector],
      );
    });

    it("validates condition tree integrity on pack", async () => {
      const { roles, evaluator, ROLE_KEY } = await loadFixture(setup);
      const selector = toFunctionSelector("doNothing()");

      await viem.assertions.revertWithCustomError(
        roles.write.allowFunctionGlobally([
          ROLE_KEY,
          selector,
          [
            {
              parent: 5, // Invalid - root node must have parent 0
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            },
          ],
        ]),
        evaluator,
        "UnsuitableRootNode",
      );
    });

    it("emits AllowFunctionGlobally event", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);
      const selector = toFunctionSelector("doNothing()");

      await viem.assertions.emitWithArgs(
        roles.write.allowFunctionGloballyPacked([ROLE_KEY, selector, "0x"]),
        roles,
        "AllowFunctionGlobally",
        [ROLE_KEY, selector, "0x"],
      );
    });

    it("overwrites existing global function permission", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = toFunctionSelector("oneParamStatic(uint256)");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);

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
          compValue: encodeAbiParameters(parseAbiParameters("uint256"), [1n]),
        },
      ]);
      await roles.write.allowFunctionGloballyPacked([
        ROLE_KEY,
        selector,
        conditionsEq1,
      ]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [2n],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
      );

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
          compValue: encodeAbiParameters(parseAbiParameters("uint256"), [2n]),
        },
      ]);
      await roles.write.allowFunctionGloballyPacked([
        ROLE_KEY,
        selector,
        conditionsEq2,
      ]);

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [2n],
          }),
          0,
        ],
        { account: member.account },
      );
    });
  });

  describe("revokeFunctionGlobally", () => {
    it("deletes global scopeConfig for selector", async () => {
      const { roles, member, testContract, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector = toFunctionSelector("doNothing()");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.allowFunctionGloballyPacked([ROLE_KEY, selector, "0x"]);

      await viem.assertions.emitWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        testContract,
        "Invoked",
        [selector],
      );

      await roles.write.revokeFunctionGlobally([ROLE_KEY, selector]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );
    });

    it("emits RevokeFunctionGlobally event", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);
      const selector = toFunctionSelector("doNothing()");

      await roles.write.allowFunctionGloballyPacked([ROLE_KEY, selector, "0x"]);

      await viem.assertions.emitWithArgs(
        roles.write.revokeFunctionGlobally([ROLE_KEY, selector]),
        roles,
        "RevokeFunctionGlobally",
        [ROLE_KEY, selector],
      );
    });

    it("does not affect other global selectors", async () => {
      const { roles, member, testContract, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const selector1 = toFunctionSelector("doNothing()");
      const selector2 = toFunctionSelector("doEvenLess()");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.allowFunctionGloballyPacked([
        ROLE_KEY,
        selector1,
        "0x",
      ]);
      await roles.write.allowFunctionGloballyPacked([
        ROLE_KEY,
        selector2,
        "0x",
      ]);

      await roles.write.revokeFunctionGlobally([ROLE_KEY, selector1]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );

      await viem.assertions.emitWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doEvenLess" }),
            0,
          ],
          { account: member.account },
        ),
        testContract,
        "Invoked",
        [selector2],
      );
    });

    it("succeeds even if global function was not allowed", async () => {
      const { roles, ROLE_KEY } = await loadFixture(setup);
      const selector = toFunctionSelector("doNothing()");

      await roles.write.revokeFunctionGlobally([ROLE_KEY, selector]);
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // ALLOWANCES
  // ═══════════════════════════════════════════════════════════════════════════

  describe("setAllowance", () => {
    it("sets balance to specified value", async () => {
      const { roles, storedAllowance } = await loadFixture(setup);

      const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        1000n,
        100n,
        3600n,
        0n,
      ]);

      const allowance = await storedAllowance(ALLOWANCE_KEY);
      assert.equal(allowance.balance, 500n);
    });

    it("sets refill to specified value", async () => {
      const { roles, storedAllowance } = await loadFixture(setup);

      const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        1000n,
        100n,
        3600n,
        0n,
      ]);

      const allowance = await storedAllowance(ALLOWANCE_KEY);
      assert.equal(allowance.refill, 100n);
    });

    it("sets period to specified value", async () => {
      const { roles, storedAllowance } = await loadFixture(setup);

      const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        1000n,
        100n,
        3600n,
        0n,
      ]);

      const allowance = await storedAllowance(ALLOWANCE_KEY);
      assert.equal(allowance.period, 3600n);
    });

    it("emits SetAllowance with the stored values, defaults resolved", async () => {
      const { roles } = await loadFixture(setup);

      const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

      const hash = await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        0n,
        100n,
        3600n,
        0n,
      ]);
      const publicClient = await viem.getPublicClient();
      const receipt = await publicClient.waitForTransactionReceipt({ hash });
      const block = await publicClient.getBlock({
        blockNumber: receipt.blockNumber,
      });

      await viem.assertions.emitWithArgs(hash, roles, "SetAllowance", [
        ALLOWANCE_KEY,
        500n,
        maxUint128,
        100n,
        3600n,
        block.timestamp,
      ]);
    });

    describe("default values", () => {
      it("sets maxRefill to max uint128 when passed 0", async () => {
        const { roles, storedAllowance } = await loadFixture(setup);

        const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

        await roles.write.setAllowance([
          ALLOWANCE_KEY,
          500n,
          0n,
          100n,
          3600n,
          0n,
        ]);

        const allowance = await storedAllowance(ALLOWANCE_KEY);
        assert.equal(allowance.maxRefill, maxUint128);
      });

      it("sets timestamp to current block.timestamp when passed 0", async () => {
        const { roles, storedAllowance } = await loadFixture(setup);

        const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

        const hash = await roles.write.setAllowance([
          ALLOWANCE_KEY,
          500n,
          1000n,
          100n,
          3600n,
          0n,
        ]);

        const publicClient = await viem.getPublicClient();
        const receipt = await publicClient.waitForTransactionReceipt({ hash });
        const block = await publicClient.getBlock({
          blockNumber: receipt.blockNumber,
        });

        const allowance = await storedAllowance(ALLOWANCE_KEY);
        assert.equal(allowance.timestamp, block.timestamp);
      });
    });

    it("overwrites all fields of existing allowance", async () => {
      const { roles, storedAllowance } = await loadFixture(setup);

      const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        1000n,
        100n,
        3600n,
        0n,
      ]);
      await time.increase(1000);
      const hash = await roles.write.setAllowance([
        ALLOWANCE_KEY,
        999n,
        2000n,
        200n,
        7200n,
        0n,
      ]);
      const publicClient = await viem.getPublicClient();
      const receipt = await publicClient.waitForTransactionReceipt({ hash });
      const block = await publicClient.getBlock({
        blockNumber: receipt.blockNumber,
      });

      const allowance = await storedAllowance(ALLOWANCE_KEY);
      assert.equal(allowance.balance, 999n);
      assert.equal(allowance.maxRefill, 2000n);
      assert.equal(allowance.refill, 200n);
      assert.equal(allowance.period, 7200n);
      assert.equal(allowance.timestamp, block.timestamp);
    });
  });

  describe("updateAllowance", () => {
    it("updates refill parameters only", async () => {
      const { roles, storedAllowance } = await loadFixture(setup);

      const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        1000n,
        100n,
        3600n,
        0n,
      ]);
      await roles.write.updateAllowance([ALLOWANCE_KEY, 2000n, 200n, 7200n]);

      const allowance = await storedAllowance(ALLOWANCE_KEY);
      assert.equal(allowance.maxRefill, 2000n);
      assert.equal(allowance.refill, 200n);
      assert.equal(allowance.period, 7200n);
    });

    it("preserves existing balance", async () => {
      const { roles, storedAllowance } = await loadFixture(setup);

      const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        1000n,
        100n,
        3600n,
        0n,
      ]);
      await roles.write.updateAllowance([ALLOWANCE_KEY, 2000n, 200n, 7200n]);

      const allowance = await storedAllowance(ALLOWANCE_KEY);
      assert.equal(allowance.balance, 500n);
    });

    it("preserves existing timestamp", async () => {
      const { roles, storedAllowance } = await loadFixture(setup);

      const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        1000n,
        100n,
        3600n,
        0n,
      ]);

      const initialAllowance = await storedAllowance(ALLOWANCE_KEY);

      await time.increase(1000);

      await roles.write.updateAllowance([ALLOWANCE_KEY, 2000n, 200n, 7200n]);

      const allowance = await storedAllowance(ALLOWANCE_KEY);
      assert.equal(allowance.timestamp, initialAllowance.timestamp);
    });

    it("emits SetAllowance with the preserved balance and timestamp", async () => {
      const { roles, storedAllowance } = await loadFixture(setup);

      const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        1000n,
        100n,
        3600n,
        0n,
      ]);
      const { timestamp } = await storedAllowance(ALLOWANCE_KEY);
      await time.increase(1000);

      await viem.assertions.emitWithArgs(
        roles.write.updateAllowance([ALLOWANCE_KEY, 0n, 200n, 7200n]),
        roles,
        "SetAllowance",
        [ALLOWANCE_KEY, 500n, maxUint128, 200n, 7200n, timestamp],
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // ADAPTERS
  // ═══════════════════════════════════════════════════════════════════════════

  describe("setTransactionUnwrapper", () => {
    it("registers unwrapper for target + selector", async () => {
      const { roles, testContractAddress } = await loadFixture(setup);

      const unwrapper = await viem.deployContract("MultiSendUnwrapper");
      const unwrapperAddress = unwrapper.address;

      const selector = toFunctionSelector("doNothing()");

      await viem.assertions.emitWithArgs(
        roles.write.setTransactionUnwrapper([
          testContractAddress,
          selector,
          unwrapperAddress,
        ]),
        roles,
        "SetUnwrapAdapter",
        [testContractAddress, selector, unwrapperAddress],
      );
    });

    it("emits SetUnwrapAdapter event", async () => {
      const { roles, testContractAddress } = await loadFixture(setup);

      const unwrapper = await viem.deployContract("MultiSendUnwrapper");
      const unwrapperAddress = unwrapper.address;

      const selector = toFunctionSelector("doNothing()");

      await viem.assertions.emitWithArgs(
        roles.write.setTransactionUnwrapper([
          testContractAddress,
          selector,
          unwrapperAddress,
        ]),
        roles,
        "SetUnwrapAdapter",
        [testContractAddress, selector, unwrapperAddress],
      );
    });

    it("can update existing unwrapper", async () => {
      const { roles, testContractAddress } = await loadFixture(setup);

      const unwrapper1 = await viem.deployContract("MultiSendUnwrapper");
      const unwrapper2 = await viem.deployContract("MultiSendUnwrapper");
      const unwrapper2Address = unwrapper2.address;

      const selector = toFunctionSelector("doNothing()");

      await roles.write.setTransactionUnwrapper([
        testContractAddress,
        selector,
        unwrapper1.address,
      ]);

      // Second call updates to unwrapper2
      await viem.assertions.emitWithArgs(
        roles.write.setTransactionUnwrapper([
          testContractAddress,
          selector,
          unwrapper2Address,
        ]),
        roles,
        "SetUnwrapAdapter",
        [testContractAddress, selector, unwrapper2Address],
      );
    });

    it("can remove unwrapper by setting to zero address", async () => {
      const { roles, testContractAddress } = await loadFixture(setup);

      const unwrapper = await viem.deployContract("MultiSendUnwrapper");
      const unwrapperAddress = unwrapper.address;

      const selector = toFunctionSelector("doNothing()");

      await roles.write.setTransactionUnwrapper([
        testContractAddress,
        selector,
        unwrapperAddress,
      ]);

      await viem.assertions.emitWithArgs(
        roles.write.setTransactionUnwrapper([
          testContractAddress,
          selector,
          zeroAddress,
        ]),
        roles,
        "SetUnwrapAdapter",
        [testContractAddress, selector, zeroAddress],
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // ISOLATION
  // ═══════════════════════════════════════════════════════════════════════════

  describe("Isolation", () => {
    it("allowing one target does not allow another target", async () => {
      const { roles, member, ROLE_KEY, testContractAddress } =
        await loadFixture(setup);

      const testContract2 = await viem.deployContract("TestContract");
      const testContract2Address = testContract2.address;

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      // testContractAddress is allowed
      await roles.write.execTransactionFromModule(
        [testContractAddress, 0n, "0x", 0],
        { account: member.account },
      );

      // testContract2Address is NOT allowed
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContract2Address, 0n, "0x", 0],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );
    });

    it("allowing one function does not allow other functions on same target", async () => {
      const { roles, member, ROLE_KEY, testContractAddress, testContract } =
        await loadFixture(setup);

      const selector1 = toFunctionSelector("doNothing()");
      const selector2 = toFunctionSelector("other()");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector1,
        "0x",
        ExecutionOptions.None,
      ]);

      // selector1 is allowed
      await viem.assertions.emitWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        testContract,
        "Invoked",
        [selector1],
      );

      // selector2 is NOT allowed
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "other" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );
    });

    it("allowing a function on one target does not allow it on another target", async () => {
      const { roles, member, ROLE_KEY, testContractAddress, testContract } =
        await loadFixture(setup);

      const testContract2 = await viem.deployContract("TestContract");
      const testContract2Address = testContract2.address;

      const selector = toFunctionSelector("doNothing()");

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);
      await roles.write.scopeTarget([ROLE_KEY, testContract2Address]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector,
        "0x",
        ExecutionOptions.None,
      ]);

      // Function on testContractAddress is allowed
      await viem.assertions.emitWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        testContract,
        "Invoked",
        [selector],
      );

      // Same function on testContract2Address is NOT allowed
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContract2Address,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );
    });

    it("multiple roles can have different permissions on same target", async () => {
      const { roles, member, ROLE_KEY, testContractAddress, testContract } =
        await loadFixture(setup);

      const ROLE_KEY_2 = keccak256(toBytes("TEST_ROLE_2"));

      const selector1 = toFunctionSelector("doNothing()");
      const selector2 = toFunctionSelector("doEvenLess()");

      // Setup: member has ROLE_KEY, grant them both roles
      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY_2,
        0n,
        0n,
        0n,
      ]);

      // ROLE_KEY: only selector1 allowed
      await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selector1,
        "0x",
        ExecutionOptions.None,
      ]);

      // ROLE_KEY_2: only selector2 allowed
      await roles.write.scopeTarget([ROLE_KEY_2, testContractAddress]);
      await roles.write.allowFunctionPacked([
        ROLE_KEY_2,
        testContractAddress,
        selector2,
        "0x",
        ExecutionOptions.None,
      ]);

      // With ROLE_KEY as default, can call selector1 but not selector2
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);

      await viem.assertions.emitWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        testContract,
        "Invoked",
        [selector1],
      );

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doEvenLess" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );

      // With ROLE_KEY_2 as default, can call selector2 but not selector1
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY_2]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );

      // selector2 is now allowed
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({ abi, functionName: "doEvenLess" }),
          0,
        ],
        { account: member.account },
      );
    });
  });
});
