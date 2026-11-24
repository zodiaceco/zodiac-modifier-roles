import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import {
  encodeAbiParameters,
  encodeFunctionData,
  keccak256,
  parseAbi,
  parseAbiParameters,
  parseEther,
  toBytes,
  toFunctionSelector,
  toHex,
  zeroAddress,
} from "viem";
import type { Address, Hex } from "viem";

import {
  ConditionViolationStatus,
  encodeMultisendPayload,
  Encoding,
  ExecutionOptions,
  type MetaTransaction,
  Operator,
  packConditions,
  type RolesContract,
} from "./utils.js";
import { createSetup } from "./setup.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { deployRolesMod, deployMultiSend } = createSetup(connection);

const abi = parseAbi([
  "function doNothing()",
  "function oneParamStatic(uint256)",
  "function twoParamsStatic(uint256, uint256)",
]);

const DO_NOTHING = toFunctionSelector("doNothing()");
const ONE_PARAM = toFunctionSelector("oneParamStatic(uint256)");

/**
 * Authorization tests
 *
 * Scope: `_authorize` and `_transaction` in `core/Authorization.sol`, and the
 * clearance state machine documented in `core/Setup.sol`.
 *
 * Structured to mirror the contract's evaluation pipeline:
 * 1. Calldata length & selector boundaries (`FunctionSignatureTooShort`, empty calldata)
 * 2. Two-step scope resolution (`Clearance.None` / `Target` / `Function`, global fallback,
 *    and clearance state transitions / entry independence)
 * 3. ExecutionOptions enforcement (`None`, `Send`, `DelegateCall`, `Both`, global)
 * 4. Condition evaluation & cross-stage check ordering
 * 5. Transaction unwrapping (`_authorize` adapter dispatch, per-entry enforcement,
 *    cumulative consumption threading, non-recursiveness)
 */

describe("Authorization", () => {
  after(async () => {
    await connection.close();
  });

  async function eqFirstParam(roles: RolesContract, expected: bigint | number) {
    return packConditions(roles, [
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
        compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
          BigInt(expected),
        ]),
      },
    ]);
  }

  async function withinAllowanceFirstParam(
    roles: RolesContract,
    allowanceKey: Hex,
  ) {
    return packConditions(roles, [
      {
        parent: 0,
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        compValue: "0x",
      },
      {
        parent: 0,
        paramType: Encoding.Static,
        operator: Operator.WithinAllowance,
        compValue: allowanceKey,
      },
    ]);
  }

  async function setup() {
    const [owner, member] = await viem.getWalletClients();

    const avatar = await viem.deployContract("TestAvatar");
    const avatarAddress = avatar.address;

    const roles = await deployRolesMod(
      owner.account.address,
      avatarAddress,
      avatarAddress,
    );

    const targetA = await viem.deployContract("TestContract");
    const targetB = await viem.deployContract("TestContract");
    const targetAddressA = targetA.address;
    const targetAddressB = targetB.address;

    const roleKey = toHex(randomBytes(32));
    await roles.write.grantRole([member.account.address, roleKey, 0n, 0n, 0n]);
    await roles.write.setDefaultRole([member.account.address, roleKey]);

    const exec = (
      to: Address,
      data: Hex = "0x",
      {
        value = 0n,
        operation = 0,
      }: { value?: bigint; operation?: number } = {},
    ) =>
      roles.write.execTransactionFromModule([to, value, data, operation], {
        account: member.account,
      });

    const fundAvatar = async (amount = parseEther("1")) => {
      await owner.sendTransaction({ to: avatarAddress, value: amount });
    };

    return {
      avatar,
      avatarAddress,
      roles,
      owner,
      member,
      targetA,
      targetB,
      targetAddressA,
      targetAddressB,
      roleKey,
      exec,
      fundAvatar,
    };
  }

  async function setupMultiSend() {
    const base = await setup();

    const { multisend, unwrapper } = await deployMultiSend(base.roles);
    const multisendAddress = multisend.address;
    const unwrapperAddress = unwrapper.address;
    const multiSendSelector = toFunctionSelector("multiSend(bytes)");

    const encodeBatch = (txs: MetaTransaction[]) =>
      encodeFunctionData({
        abi: multisend.abi,
        functionName: "multiSend",
        args: [encodeMultisendPayload(txs)],
      });

    return {
      ...base,
      multisend,
      multisendAddress,
      multiSendSelector,
      unwrapper,
      unwrapperAddress,
      encodeBatch,
    };
  }

  // ═══════════════════════════════════════════════════════════════════════════
  // 1. CALLDATA LENGTH & SELECTOR BOUNDARIES
  // ═══════════════════════════════════════════════════════════════════════════

  describe("calldata length", () => {
    it("allows empty calldata (0 bytes) under Clearance.Target", async () => {
      const { roles, targetA, targetAddressA, roleKey, exec } =
        await loadFixture(setup);

      await roles.write.allowTargetPacked([
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      ]);

      await viem.assertions.emitWithArgs(
        exec(targetAddressA, "0x"),
        targetA,
        "Invoked",
        ["0x00000000"],
      );
    });

    it("reverts with FunctionSignatureTooShort for 1-3 bytes across clearance modes", async () => {
      const { roles, targetAddressA, roleKey, exec } = await loadFixture(setup);

      const shortPayloads = ["0x12", "0x1234", "0x123456"] as const;

      // Clearance.None (even with a global rule present)
      await roles.write.allowFunctionGloballyPacked([
        roleKey,
        DO_NOTHING,
        "0x",
      ]);
      for (const data of shortPayloads) {
        await viem.assertions.revertWithCustomError(
          exec(targetAddressA, data),
          roles,
          "FunctionSignatureTooShort",
        );
      }

      // Clearance.Function
      await roles.write.scopeTarget([roleKey, targetAddressA]);
      for (const data of shortPayloads) {
        await viem.assertions.revertWithCustomError(
          exec(targetAddressA, data),
          roles,
          "FunctionSignatureTooShort",
        );
      }

      // Clearance.Target
      await roles.write.allowTargetPacked([
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      ]);
      for (const data of shortPayloads) {
        await viem.assertions.revertWithCustomError(
          exec(targetAddressA, data),
          roles,
          "FunctionSignatureTooShort",
        );
      }
    });

    it("does not match empty calldata to selector 0x00000000 under Clearance.Function", async () => {
      const { roles, targetA, targetAddressA, roleKey, exec, fundAvatar } =
        await loadFixture(setup);

      await roles.write.scopeTarget([roleKey, targetAddressA]);
      await roles.write.allowFunctionPacked([
        roleKey,
        targetAddressA,
        "0x00000000",
        "0x",
        ExecutionOptions.Send,
      ]);
      await fundAvatar();

      // Explicit 4-byte 0x00000000 selector is allowed
      await viem.assertions.emitWithArgs(
        exec(targetAddressA, "0x00000000"),
        targetA,
        "Invoked",
        ["0x00000000"],
      );

      // Empty calldata must not match selector 0x00000000
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(targetAddressA, "0x"),
        roles,
        "TransactionNotAllowed",
        [targetAddressA, "0x00000000"],
      );

      // Empty calldata ETH transfer must also be rejected
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(targetAddressA, "0x", { value: parseEther("0.5") }),
        roles,
        "TransactionNotAllowed",
        [targetAddressA, "0x00000000"],
      );
    });

    it("does not match empty calldata to global selector 0x00000000", async () => {
      const { roles, targetA, targetAddressA, roleKey, exec } =
        await loadFixture(setup);

      await roles.write.allowFunctionGloballyPacked([
        roleKey,
        "0x00000000",
        "0x",
      ]);

      // Explicit 4-byte 0x00000000 selector resolves via global rule
      await viem.assertions.emitWithArgs(
        exec(targetAddressA, "0x00000000"),
        targetA,
        "Invoked",
        ["0x00000000"],
      );

      // Empty calldata must skip global lookup
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(targetAddressA, "0x"),
        roles,
        "TransactionNotAllowed",
        [targetAddressA, "0x00000000"],
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // 2. SCOPE RESOLUTION & CLEARANCE STATE MACHINE
  // ═══════════════════════════════════════════════════════════════════════════

  describe("scope resolution", () => {
    describe("Clearance.None", () => {
      it("reverts with TransactionNotAllowed when no global rule exists", async () => {
        const { roles, targetAddressA, exec } = await loadFixture(setup);

        await viem.assertions.revertWithCustomErrorWithArgs(
          exec(targetAddressA, "0x"),
          roles,
          "TransactionNotAllowed",
          [targetAddressA, "0x00000000"],
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          roles,
          "TransactionNotAllowed",
          [targetAddressA, DO_NOTHING],
        );
      });

      it("resolves to global function entry on any target", async () => {
        const {
          roles,
          targetA,
          targetB,
          targetAddressA,
          targetAddressB,
          roleKey,
          exec,
        } = await loadFixture(setup);

        await roles.write.allowFunctionGloballyPacked([
          roleKey,
          DO_NOTHING,
          "0x",
        ]);

        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          targetA,
          "Invoked",
          [DO_NOTHING],
        );

        await viem.assertions.emitWithArgs(
          exec(
            targetAddressB,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          targetB,
          "Invoked",
          [DO_NOTHING],
        );
      });
    });

    describe("Clearance.Target", () => {
      it("allows any function on target", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.write.allowTargetPacked([
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        ]);

        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          targetA,
          "Invoked",
          [DO_NOTHING],
        );

        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          targetA,
          "Invoked",
          [ONE_PARAM],
        );
      });

      it("takes precedence over a looser global function entry", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        // Target-specific: first param must equal 42
        await roles.write.allowTargetPacked([
          roleKey,
          targetAddressA,
          await eqFirstParam(roles, 42),
          ExecutionOptions.None,
        ]);
        // Global: unconstrained
        await roles.write.allowFunctionGloballyPacked([
          roleKey,
          ONE_PARAM,
          "0x",
        ]);

        // 42 passes via target entry
        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          targetA,
          "Invoked",
          [ONE_PARAM],
        );

        // 99 fails — target rule governs, does not fall through to global
        await viem.assertions.revertWithCustomErrorWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [99n],
            }),
          ),
          roles,
          "ConditionViolation",
          [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
        );
      });
    });

    describe("Clearance.Function", () => {
      it("allows only permitted selectors and reverts TransactionNotAllowed for others", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.write.scopeTarget([roleKey, targetAddressA]);
        await roles.write.allowFunctionPacked([
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        ]);

        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          targetA,
          "Invoked",
          [DO_NOTHING],
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          roles,
          "TransactionNotAllowed",
          [targetAddressA, ONE_PARAM],
        );
      });

      it("takes precedence over a global function entry for the same selector", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        // Target-specific: param must equal 42
        await roles.write.scopeTarget([roleKey, targetAddressA]);
        await roles.write.allowFunctionPacked([
          roleKey,
          targetAddressA,
          ONE_PARAM,
          await eqFirstParam(roles, 42),
          ExecutionOptions.None,
        ]);
        // Global: unconstrained
        await roles.write.allowFunctionGloballyPacked([
          roleKey,
          ONE_PARAM,
          "0x",
        ]);

        // 42 passes via function rule
        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          targetA,
          "Invoked",
          [ONE_PARAM],
        );

        // 99 fails — target-specific function rule governs, not global
        await viem.assertions.revertWithCustomErrorWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [99n],
            }),
          ),
          roles,
          "ConditionViolation",
          [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
        );
      });

      it("falls back to global function entry when selector is not configured on target", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.write.scopeTarget([roleKey, targetAddressA]);
        await roles.write.allowFunctionPacked([
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        ]);
        await roles.write.allowFunctionGloballyPacked([
          roleKey,
          ONE_PARAM,
          "0x",
        ]);

        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          targetA,
          "Invoked",
          [ONE_PARAM],
        );
      });

      it("does not collide selector 0xffffffff with Target scope entry", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        const maxSelector = "0xffffffff" as const;
        const payload = (n: number) =>
          (maxSelector +
            encodeAbiParameters(parseAbiParameters("uint256"), [
              BigInt(n),
            ]).slice(2)) as Hex;

        // Target entry requires param == 100
        await roles.write.allowTargetPacked([
          roleKey,
          targetAddressA,
          await eqFirstParam(roles, 100),
          ExecutionOptions.None,
        ]);
        // Function entry for 0xffffffff requires param == 42 (must not clobber target entry)
        await roles.write.allowFunctionPacked([
          roleKey,
          targetAddressA,
          maxSelector,
          await eqFirstParam(roles, 42),
          ExecutionOptions.None,
        ]);

        // While Clearance.Target: target entry (100) governs
        await viem.assertions.emitWithArgs(
          exec(targetAddressA, payload(100)),
          targetA,
          "Invoked",
          [maxSelector],
        );
        await viem.assertions.revertWithCustomError(
          exec(targetAddressA, payload(42)),
          roles,
          "ConditionViolation",
        );

        // Switch to Clearance.Function: function entry (42) governs
        await roles.write.scopeTarget([roleKey, targetAddressA]);
        await viem.assertions.emitWithArgs(
          exec(targetAddressA, payload(42)),
          targetA,
          "Invoked",
          [maxSelector],
        );
        await viem.assertions.revertWithCustomError(
          exec(targetAddressA, payload(100)),
          roles,
          "ConditionViolation",
        );
      });
    });

    describe("clearance state machine & entry independence", () => {
      it("Target -> Function: scopeTarget tightens previously allowed target", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.write.allowTargetPacked([
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        ]);
        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          targetA,
          "Invoked",
          [ONE_PARAM],
        );

        await roles.write.scopeTarget([roleKey, targetAddressA]);
        await roles.write.allowFunctionPacked([
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        ]);

        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          targetA,
          "Invoked",
          [DO_NOTHING],
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          roles,
          "TransactionNotAllowed",
          [targetAddressA, ONE_PARAM],
        );
      });

      it("Function -> Target: allowTarget loosens previously scoped target", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.write.scopeTarget([roleKey, targetAddressA]);
        await roles.write.allowFunctionPacked([
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        ]);

        await viem.assertions.revertWithCustomError(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          roles,
          "TransactionNotAllowed",
        );

        await roles.write.allowTargetPacked([
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        ]);

        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          targetA,
          "Invoked",
          [ONE_PARAM],
        );
      });

      it("Function -> Target -> Function: prior function entries reactivate when re-scoped", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.write.scopeTarget([roleKey, targetAddressA]);
        await roles.write.allowFunctionPacked([
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        ]);

        // Loosen to Target, then tighten back to Function without re-calling allowFunction
        await roles.write.allowTargetPacked([
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        ]);
        await roles.write.scopeTarget([roleKey, targetAddressA]);

        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          targetA,
          "Invoked",
          [DO_NOTHING],
        );

        await viem.assertions.revertWithCustomError(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          roles,
          "TransactionNotAllowed",
        );
      });

      it("Function -> None: revokeTarget disables function entries while leaving global fallback active", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.write.scopeTarget([roleKey, targetAddressA]);
        await roles.write.allowFunctionPacked([
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        ]);
        await roles.write.allowFunctionGloballyPacked([
          roleKey,
          ONE_PARAM,
          "0x",
        ]);

        await roles.write.revokeTarget([roleKey, targetAddressA]);

        // Target-scoped doNothing is now disabled
        await viem.assertions.revertWithCustomError(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          roles,
          "TransactionNotAllowed",
        );

        // Global oneParamStatic still authorizes under Clearance.None
        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          targetA,
          "Invoked",
          [ONE_PARAM],
        );
      });

      it("Target -> None: revokeTarget disables target entry while leaving global fallback active", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.write.allowTargetPacked([
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        ]);
        await roles.write.allowFunctionGloballyPacked([
          roleKey,
          ONE_PARAM,
          "0x",
        ]);

        await roles.write.revokeTarget([roleKey, targetAddressA]);

        // Target-level doNothing is disabled
        await viem.assertions.revertWithCustomError(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          roles,
          "TransactionNotAllowed",
        );

        // Global oneParamStatic still authorizes
        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [42n],
            }),
          ),
          targetA,
          "Invoked",
          [ONE_PARAM],
        );
      });

      it("allowFunction written while Clearance.None stays dormant until scopeTarget", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        // Write function entry before scoping target
        await roles.write.allowFunctionPacked([
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        ]);

        // Dormant under Clearance.None
        await viem.assertions.revertWithCustomError(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          roles,
          "TransactionNotAllowed",
        );

        // Activates once scoped
        await roles.write.scopeTarget([roleKey, targetAddressA]);
        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          targetA,
          "Invoked",
          [DO_NOTHING],
        );
      });

      it("revokeFunction clears only target-specific entry, exposing global fallback", async () => {
        const {
          roles,
          targetA,
          targetB,
          targetAddressA,
          targetAddressB,
          roleKey,
          exec,
        } = await loadFixture(setup);

        // Target-specific requires param == 42; global is unconstrained
        await roles.write.scopeTarget([roleKey, targetAddressA]);
        await roles.write.allowFunctionPacked([
          roleKey,
          targetAddressA,
          ONE_PARAM,
          await eqFirstParam(roles, 42),
          ExecutionOptions.None,
        ]);
        await roles.write.allowFunctionGloballyPacked([
          roleKey,
          ONE_PARAM,
          "0x",
        ]);

        await roles.write.revokeFunction([roleKey, targetAddressA, ONE_PARAM]);

        // Target-specific constraint is gone — global fallback allows param == 99
        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [99n],
            }),
          ),
          targetA,
          "Invoked",
          [ONE_PARAM],
        );

        // Global still works on other targets
        await viem.assertions.emitWithArgs(
          exec(
            targetAddressB,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [99n],
            }),
          ),
          targetB,
          "Invoked",
          [ONE_PARAM],
        );
      });

      it("revokeFunctionGlobally clears only global entry, preserving target-specific entry", async () => {
        const {
          roles,
          targetA,
          targetAddressA,
          targetAddressB,
          roleKey,
          exec,
        } = await loadFixture(setup);

        await roles.write.scopeTarget([roleKey, targetAddressA]);
        await roles.write.allowFunctionPacked([
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        ]);
        await roles.write.allowFunctionGloballyPacked([
          roleKey,
          DO_NOTHING,
          "0x",
        ]);

        await roles.write.revokeFunctionGlobally([roleKey, DO_NOTHING]);

        // Target-specific still works
        await viem.assertions.emitWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          targetA,
          "Invoked",
          [DO_NOTHING],
        );

        // Global no longer works on other targets
        await viem.assertions.revertWithCustomError(
          exec(
            targetAddressB,
            encodeFunctionData({ abi, functionName: "doNothing" }),
          ),
          roles,
          "TransactionNotAllowed",
        );
      });
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // 3. EXECUTION OPTIONS
  // ═══════════════════════════════════════════════════════════════════════════

  describe("execution options", () => {
    const scopes = [
      {
        label: "Clearance.Target",
        data: "0x" as Hex,
        expectedSelector: "0x00000000" as Hex,
        configure: async (
          roles: RolesContract,
          roleKey: Hex,
          target: Address,
          options: ExecutionOptions,
        ) => {
          await roles.write.allowTargetPacked([roleKey, target, "0x", options]);
        },
      },
      {
        label: "Clearance.Function",
        data: encodeFunctionData({ abi, functionName: "doNothing" }),
        expectedSelector: DO_NOTHING,
        configure: async (
          roles: RolesContract,
          roleKey: Hex,
          target: Address,
          options: ExecutionOptions,
        ) => {
          await roles.write.scopeTarget([roleKey, target]);
          await roles.write.allowFunctionPacked([
            roleKey,
            target,
            DO_NOTHING,
            "0x",
            options,
          ]);
        },
      },
    ];

    for (const scope of scopes) {
      describe(scope.label, () => {
        it("None: allows Call(0), blocks Send and DelegateCall", async () => {
          const { roles, targetA, targetAddressA, roleKey, exec, fundAvatar } =
            await loadFixture(setup);

          await scope.configure(
            roles,
            roleKey,
            targetAddressA,
            ExecutionOptions.None,
          );
          await fundAvatar();

          await viem.assertions.emitWithArgs(
            exec(targetAddressA, scope.data),
            targetA,
            "Invoked",
            [scope.expectedSelector],
          );

          await viem.assertions.revertWithCustomErrorWithArgs(
            exec(targetAddressA, scope.data, {
              value: parseEther("0.1"),
            }),
            roles,
            "SendNotAllowed",
            [targetAddressA],
          );

          await viem.assertions.revertWithCustomErrorWithArgs(
            exec(targetAddressA, scope.data, { operation: 1 }),
            roles,
            "DelegateCallNotAllowed",
            [targetAddressA],
          );
        });

        it("Send: allows value transfer, still blocks DelegateCall", async () => {
          const {
            roles,
            avatarAddress,
            targetA,
            targetAddressA,
            roleKey,
            exec,
            fundAvatar,
          } = await loadFixture(setup);

          await scope.configure(
            roles,
            roleKey,
            targetAddressA,
            ExecutionOptions.Send,
          );
          await fundAvatar();

          const amount = parseEther("0.1");
          await viem.assertions.balancesHaveChanged(
            exec(targetAddressA, scope.data, { value: amount }),
            [
              { address: avatarAddress, amount: -amount },
              { address: targetAddressA, amount },
            ],
          );

          await viem.assertions.revertWithCustomErrorWithArgs(
            exec(targetAddressA, scope.data, { operation: 1 }),
            roles,
            "DelegateCallNotAllowed",
            [targetAddressA],
          );

          // Verify zero-value Call also still works
          await viem.assertions.emitWithArgs(
            exec(targetAddressA, scope.data),
            targetA,
            "Invoked",
            [scope.expectedSelector],
          );
        });

        it("DelegateCall: allows DelegateCall and Call(0), still blocks Send", async () => {
          const {
            roles,
            avatarAddress,
            targetA,
            targetAddressA,
            roleKey,
            exec,
            fundAvatar,
          } = await loadFixture(setup);

          await scope.configure(
            roles,
            roleKey,
            targetAddressA,
            ExecutionOptions.DelegateCall,
          );
          await fundAvatar();

          // DelegateCall executes in avatar's context
          const avatarTarget = await viem.getContractAt(
            "TestContract",
            avatarAddress,
          );
          await viem.assertions.emitWithArgs(
            exec(targetAddressA, scope.data, { operation: 1 }),
            avatarTarget,
            "Invoked",
            [scope.expectedSelector],
          );

          // Regular Call with 0 value still works
          await viem.assertions.emitWithArgs(
            exec(targetAddressA, scope.data),
            targetA,
            "Invoked",
            [scope.expectedSelector],
          );

          // Sending ETH value is still blocked
          await viem.assertions.revertWithCustomErrorWithArgs(
            exec(targetAddressA, scope.data, {
              value: parseEther("0.1"),
            }),
            roles,
            "SendNotAllowed",
            [targetAddressA],
          );
        });

        it("Both: allows Send, DelegateCall, and both together", async () => {
          const {
            roles,
            avatarAddress,
            targetAddressA,
            roleKey,
            exec,
            fundAvatar,
          } = await loadFixture(setup);

          await scope.configure(
            roles,
            roleKey,
            targetAddressA,
            ExecutionOptions.Both,
          );
          await fundAvatar();

          const amount = parseEther("0.1");
          await viem.assertions.balancesHaveChanged(
            exec(targetAddressA, scope.data, { value: amount }),
            [
              { address: avatarAddress, amount: -amount },
              { address: targetAddressA, amount },
            ],
          );

          const avatarTarget = await viem.getContractAt(
            "TestContract",
            avatarAddress,
          );
          await viem.assertions.emitWithArgs(
            exec(targetAddressA, scope.data, { operation: 1 }),
            avatarTarget,
            "Invoked",
            [scope.expectedSelector],
          );

          // Combined value > 0 and DelegateCall passes both option checks
          await viem.assertions.emitWithArgs(
            exec(targetAddressA, scope.data, { value: amount, operation: 1 }),
            avatarTarget,
            "Invoked",
            [scope.expectedSelector],
          );
        });
      });
    }

    describe("global function entry", () => {
      it("always blocks Send and DelegateCall while allowing Call(0)", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec, fundAvatar } =
          await loadFixture(setup);

        await roles.write.allowFunctionGloballyPacked([
          roleKey,
          DO_NOTHING,
          "0x",
        ]);
        await fundAvatar();

        const data = encodeFunctionData({ abi, functionName: "doNothing" });

        await viem.assertions.revertWithCustomErrorWithArgs(
          exec(targetAddressA, data, { value: 1n }),
          roles,
          "SendNotAllowed",
          [targetAddressA],
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          exec(targetAddressA, data, { operation: 1 }),
          roles,
          "DelegateCallNotAllowed",
          [targetAddressA],
        );

        await viem.assertions.emitWithArgs(
          exec(targetAddressA, data),
          targetA,
          "Invoked",
          [DO_NOTHING],
        );
      });
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // 4. CONDITION EVALUATION & CHECK ORDERING
  // ═══════════════════════════════════════════════════════════════════════════

  describe("condition evaluation & check ordering", () => {
    it("evaluates target-level condition regardless of which function is called", async () => {
      const { roles, targetA, targetAddressA, roleKey, exec } =
        await loadFixture(setup);

      await roles.write.allowTargetPacked([
        roleKey,
        targetAddressA,
        await eqFirstParam(roles, 100),
        ExecutionOptions.None,
      ]);

      await viem.assertions.emitWithArgs(
        exec(
          targetAddressA,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [100n],
          }),
        ),
        targetA,
        "Invoked",
        [ONE_PARAM],
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(
          targetAddressA,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [50n],
          }),
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );

      await exec(
        targetAddressA,
        encodeFunctionData({
          abi,
          functionName: "twoParamsStatic",
          args: [100n, 999n],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(
          targetAddressA,
          encodeFunctionData({
            abi,
            functionName: "twoParamsStatic",
            args: [200n, 999n],
          }),
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );
    });

    it("evaluates function-specific conditions", async () => {
      const { roles, targetA, targetAddressA, roleKey, exec } =
        await loadFixture(setup);

      await roles.write.scopeTarget([roleKey, targetAddressA]);
      await roles.write.allowFunctionPacked([
        roleKey,
        targetAddressA,
        ONE_PARAM,
        await eqFirstParam(roles, 42),
        ExecutionOptions.None,
      ]);

      await viem.assertions.emitWithArgs(
        exec(
          targetAddressA,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [42n],
          }),
        ),
        targetA,
        "Invoked",
        [ONE_PARAM],
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(
          targetAddressA,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [99n],
          }),
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );
    });

    it("evaluates global function conditions", async () => {
      const { roles, targetA, targetAddressA, roleKey, exec } =
        await loadFixture(setup);

      await roles.write.allowFunctionGloballyPacked([
        roleKey,
        ONE_PARAM,
        await eqFirstParam(roles, 100),
      ]);

      await viem.assertions.emitWithArgs(
        exec(
          targetAddressA,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [100n],
          }),
        ),
        targetA,
        "Invoked",
        [ONE_PARAM],
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(
          targetAddressA,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [50n],
          }),
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );
    });

    describe("check ordering", () => {
      it("reverts SendNotAllowed before DelegateCallNotAllowed when both are disallowed", async () => {
        const { roles, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.write.allowTargetPacked([
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          exec(
            targetAddressA,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            {
              value: 1n,
              operation: 1,
            },
          ),
          roles,
          "SendNotAllowed",
          [targetAddressA],
        );
      });

      it("enforces ExecutionOptions before evaluating conditions", async () => {
        const { roles, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.write.allowTargetPacked([
          roleKey,
          targetAddressA,
          await eqFirstParam(roles, 42),
          ExecutionOptions.None,
        ]);

        const violatingData = encodeFunctionData({
          abi,
          functionName: "oneParamStatic",
          args: [99n],
        });

        await viem.assertions.revertWithCustomErrorWithArgs(
          exec(targetAddressA, violatingData, { value: 1n }),
          roles,
          "SendNotAllowed",
          [targetAddressA],
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          exec(targetAddressA, violatingData, { operation: 1 }),
          roles,
          "DelegateCallNotAllowed",
          [targetAddressA],
        );
      });
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // 5. TRANSACTION UNWRAPPING
  // ═══════════════════════════════════════════════════════════════════════════

  describe("transaction unwrapping", () => {
    it("unwraps and authorizes batch transactions without requiring clearance on MultiSend", async () => {
      const {
        roles,
        targetA,
        targetAddressA,
        roleKey,
        exec,
        multisendAddress,
        encodeBatch,
      } = await loadFixture(setupMultiSend);

      await roles.write.allowTargetPacked([
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      ]);

      const batchData = encodeBatch([
        {
          to: targetAddressA,
          value: 0n,
          operation: 0,
          data: encodeFunctionData({ abi, functionName: "doNothing" }),
        },
        {
          to: targetAddressA,
          value: 0n,
          operation: 0,
          data: encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [42n],
          }),
        },
      ]);

      const hash = await exec(multisendAddress, batchData, { operation: 1 });
      await viem.assertions.emitWithArgs(hash, targetA, "Invoked", [
        DO_NOTHING,
      ]);
      await viem.assertions.emitWithArgs(hash, targetA, "Invoked", [ONE_PARAM]);
    });

    it("does not match short calldata (< 4 bytes) to an unwrapper", async () => {
      const {
        roles,
        targetA,
        targetAddressA,
        roleKey,
        exec,
        unwrapperAddress,
      } = await loadFixture(setupMultiSend);

      await roles.write.allowTargetPacked([
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      ]);

      // Register unwrappers for selectors with trailing zero bytes
      for (const selector of [
        "0x00000000",
        "0x12000000",
        "0x12340000",
        "0x12345600",
      ] as const) {
        await roles.write.setTransactionUnwrapper([
          targetAddressA,
          selector,
          unwrapperAddress,
        ]);
      }

      // 0 bytes bypasses unwrapper lookup and succeeds under Clearance.Target
      await viem.assertions.emitWithArgs(
        exec(targetAddressA, "0x"),
        targetA,
        "Invoked",
        ["0x00000000"],
      );

      // 1-3 bytes bypass unwrapper lookup and revert FunctionSignatureTooShort
      for (const shortData of ["0x12", "0x1234", "0x123456"] as const) {
        await viem.assertions.revertWithCustomError(
          exec(targetAddressA, shortData),
          roles,
          "FunctionSignatureTooShort",
        );
      }
    });

    it("reverts MalformedMultiEntrypoint when unwrapper rejects payload, value, or operation", async () => {
      const {
        roles,
        targetAddressA,
        roleKey,
        exec,
        fundAvatar,
        multisend,
        multisendAddress,
        encodeBatch,
      } = await loadFixture(setupMultiSend);

      await roles.write.allowTargetPacked([
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      ]);
      await fundAvatar();

      // Empty multisend payload
      const emptyPayload = encodeFunctionData({
        abi: multisend.abi,
        functionName: "multiSend",
        args: ["0x"],
      });
      await viem.assertions.revertWithCustomError(
        exec(multisendAddress, emptyPayload, { operation: 1 }),
        roles,
        "MalformedMultiEntrypoint",
      );

      const validBatch = encodeBatch([
        {
          to: targetAddressA,
          value: 0n,
          operation: 0,
          data: encodeFunctionData({ abi, functionName: "doNothing" }),
        },
      ]);

      // Outer Call instead of DelegateCall
      await viem.assertions.revertWithCustomError(
        exec(multisendAddress, validBatch, { operation: 0 }),
        roles,
        "MalformedMultiEntrypoint",
      );

      // Non-zero outer ETH value
      await viem.assertions.revertWithCustomError(
        exec(multisendAddress, validBatch, { value: 1n, operation: 1 }),
        roles,
        "MalformedMultiEntrypoint",
      );
    });

    it("enforces clearance, execution options, conditions, and calldata length on each unwrapped entry", async () => {
      const {
        roles,
        targetAddressA,
        targetAddressB,
        roleKey,
        exec,
        fundAvatar,
        multisendAddress,
        encodeBatch,
      } = await loadFixture(setupMultiSend);

      await roles.write.scopeTarget([roleKey, targetAddressA]);
      await roles.write.allowFunctionPacked([
        roleKey,
        targetAddressA,
        ONE_PARAM,
        await eqFirstParam(roles, 42),
        ExecutionOptions.None,
      ]);
      await fundAvatar();

      const validEntry: MetaTransaction = {
        to: targetAddressA,
        value: 0n,
        operation: 0,
        data: encodeFunctionData({
          abi,
          functionName: "oneParamStatic",
          args: [42n],
        }),
      };

      // Unauthorized inner target
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(
          multisendAddress,
          encodeBatch([
            validEntry,
            {
              to: targetAddressB,
              value: 0n,
              operation: 0,
              data: encodeFunctionData({ abi, functionName: "doNothing" }),
            },
          ]),
          { operation: 1 },
        ),
        roles,
        "TransactionNotAllowed",
        [targetAddressB, DO_NOTHING],
      );

      // Disallowed inner value transfer
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(
          multisendAddress,
          encodeBatch([validEntry, { ...validEntry, value: 1n }]),
          { operation: 1 },
        ),
        roles,
        "SendNotAllowed",
        [targetAddressA],
      );

      // Disallowed inner DelegateCall
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(
          multisendAddress,
          encodeBatch([validEntry, { ...validEntry, operation: 1 }]),
          { operation: 1 },
        ),
        roles,
        "DelegateCallNotAllowed",
        [targetAddressA],
      );

      // Inner condition violation
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(
          multisendAddress,
          encodeBatch([
            validEntry,
            {
              to: targetAddressA,
              value: 0n,
              operation: 0,
              data: encodeFunctionData({
                abi,
                functionName: "oneParamStatic",
                args: [99n],
              }),
            },
          ]),
          { operation: 1 },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );

      // Inner short calldata (1-3 bytes)
      await viem.assertions.revertWithCustomError(
        exec(
          multisendAddress,
          encodeBatch([
            validEntry,
            { to: targetAddressA, value: 0n, operation: 0, data: "0x1234" },
          ]),
          { operation: 1 },
        ),
        roles,
        "FunctionSignatureTooShort",
      );
    });

    it("threads allowance consumption across unwrapped entries and rejects when cumulative spend exceeds balance", async () => {
      const {
        roles,
        targetAddressA,
        roleKey,
        exec,
        multisendAddress,
        encodeBatch,
      } = await loadFixture(setupMultiSend);

      const ALLOWANCE_KEY = keccak256(toBytes("BATCH_ALLOWANCE"));
      await roles.write.setAllowance([ALLOWANCE_KEY, 1000n, 0n, 0n, 0n, 0n]);

      await roles.write.scopeTarget([roleKey, targetAddressA]);
      await roles.write.allowFunctionPacked([
        roleKey,
        targetAddressA,
        ONE_PARAM,
        await withinAllowanceFirstParam(roles, ALLOWANCE_KEY),
        ExecutionOptions.None,
      ]);

      // 100 + 200 = 300 <= 1000 succeeds and settles to 700
      const okBatch = encodeBatch([
        {
          to: targetAddressA,
          value: 0n,
          operation: 0,
          data: encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [100n],
          }),
        },
        {
          to: targetAddressA,
          value: 0n,
          operation: 0,
          data: encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [200n],
          }),
        },
      ]);
      await viem.assertions.emitWithArgs(
        exec(multisendAddress, okBatch, { operation: 1 }),
        roles,
        "ConsumeAllowance",
        [ALLOWANCE_KEY, 300n, 700n],
      );

      // 400 + 400 = 800 > 700 rejects on the second entry before execution
      const overflowBatch = encodeBatch([
        {
          to: targetAddressA,
          value: 0n,
          operation: 0,
          data: encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [400n],
          }),
        },
        {
          to: targetAddressA,
          value: 0n,
          operation: 0,
          data: encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [400n],
          }),
        },
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(multisendAddress, overflowBatch, { operation: 1 }),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 1n, anyValue],
      );

      assert.equal(
        (await roles.read.accruedAllowance([ALLOWANCE_KEY]))[0],
        700n,
      );
    });

    it("does not recursively unwrap nested bundles", async () => {
      const {
        roles,
        targetAddressA,
        roleKey,
        exec,
        multisendAddress,
        multiSendSelector,
        encodeBatch,
      } = await loadFixture(setupMultiSend);

      await roles.write.allowTargetPacked([
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      ]);

      const innerBatch = encodeBatch([
        {
          to: targetAddressA,
          value: 0n,
          operation: 0,
          data: encodeFunctionData({ abi, functionName: "doNothing" }),
        },
      ]);
      const outerBatch = encodeBatch([
        {
          to: multisendAddress,
          value: 0n,
          operation: 1,
          data: innerBatch,
        },
      ]);

      // Inner call to MultiSend is checked via _transaction, not unwrapped again
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(multisendAddress, outerBatch, { operation: 1 }),
        roles,
        "TransactionNotAllowed",
        [multisendAddress, multiSendSelector],
      );
    });

    it("restores normal transaction authorization when unwrapper is removed", async () => {
      const {
        roles,
        targetAddressA,
        roleKey,
        exec,
        multisendAddress,
        multiSendSelector,
        encodeBatch,
      } = await loadFixture(setupMultiSend);

      await roles.write.allowTargetPacked([
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      ]);

      // Remove unwrapper
      await roles.write.setTransactionUnwrapper([
        multisendAddress,
        multiSendSelector,
        zeroAddress,
      ]);

      const batchData = encodeBatch([
        {
          to: targetAddressA,
          value: 0n,
          operation: 0,
          data: encodeFunctionData({ abi, functionName: "doNothing" }),
        },
      ]);

      // Now goes directly through _transaction, where MultiSend has Clearance.None
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(multisendAddress, batchData, { operation: 1 }),
        roles,
        "TransactionNotAllowed",
        [multisendAddress, multiSendSelector],
      );
    });
  });
});
