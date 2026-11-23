import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { AbiCoder, hexlify, Interface, randomBytes, ZeroAddress } from "ethers";
import { network } from "hardhat";

import type { Roles } from "../typechain-types/contracts/Roles.js";
import {
  ConditionViolationStatus,
  encodeMultisendPayload,
  Encoding,
  ExecutionOptions,
  Operator,
  packConditions,
} from "./utils.js";
import { createSetup } from "./setup.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { deployRolesMod } = createSetup(connection);

const abiCoder = AbiCoder.defaultAbiCoder();

const iface = new Interface([
  "function doNothing()",
  "function oneParamStatic(uint256)",
  "function twoParamsStatic(uint256, uint256)",
]);

const DO_NOTHING = iface.getFunction("doNothing")!.selector;
const ONE_PARAM = iface.getFunction("oneParamStatic")!.selector;

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

  async function eqFirstParam(roles: Roles, expected: bigint | number) {
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
        compValue: abiCoder.encode(["uint256"], [expected]),
      },
    ]);
  }

  async function withinAllowanceFirstParam(roles: Roles, allowanceKey: string) {
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
    const [owner, member] = await ethers.getSigners();

    const Avatar = await ethers.getContractFactory("TestAvatar");
    const avatar = await Avatar.deploy();
    const avatarAddress = await avatar.getAddress();

    const roles = await deployRolesMod(
      owner.address,
      avatarAddress,
      avatarAddress,
    );

    const TestContract = await ethers.getContractFactory("TestContract");
    const targetA = await TestContract.deploy();
    const targetB = await TestContract.deploy();
    const targetAddressA = await targetA.getAddress();
    const targetAddressB = await targetB.getAddress();

    const roleKey = hexlify(randomBytes(32));
    await roles.grantRole(member.address, roleKey, 0, 0, 0);
    await roles.setDefaultRole(member.address, roleKey);

    const exec = (
      to: string,
      data = "0x",
      {
        value = 0n,
        operation = 0,
      }: { value?: bigint; operation?: number } = {},
    ) =>
      roles
        .connect(member)
        .execTransactionFromModule(to, value, data, operation);

    const fundAvatar = async (amount = ethers.parseEther("1")) => {
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

    const MultiSend = await ethers.getContractFactory("MultiSend");
    const multisend = await MultiSend.deploy();
    const multisendAddress = await multisend.getAddress();

    const MultiSendUnwrapper =
      await ethers.getContractFactory("MultiSendUnwrapper");
    const unwrapper = await MultiSendUnwrapper.deploy();
    const unwrapperAddress = await unwrapper.getAddress();

    const multiSendSelector =
      multisend.interface.getFunction("multiSend").selector;

    await base.roles.setTransactionUnwrapper(
      multisendAddress,
      multiSendSelector,
      unwrapperAddress,
    );

    const encodeBatch = (txs: Parameters<typeof encodeMultisendPayload>[0]) =>
      multisend.interface.encodeFunctionData("multiSend", [
        encodeMultisendPayload(txs),
      ]);

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

      await roles.allowTargetPacked(
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      );

      await expect(exec(targetAddressA, "0x"))
        .to.emit(targetA, "Invoked")
        .withArgs("0x00000000");
    });

    it("reverts with FunctionSignatureTooShort for 1-3 bytes across clearance modes", async () => {
      const { roles, targetAddressA, roleKey, exec } = await loadFixture(setup);

      const shortPayloads = ["0x12", "0x1234", "0x123456"];

      // Clearance.None (even with a global rule present)
      await roles.allowFunctionGloballyPacked(roleKey, DO_NOTHING, "0x");
      for (const data of shortPayloads) {
        await expect(exec(targetAddressA, data)).to.be.revertedWithCustomError(
          roles,
          "FunctionSignatureTooShort",
        );
      }

      // Clearance.Function
      await roles.scopeTarget(roleKey, targetAddressA);
      for (const data of shortPayloads) {
        await expect(exec(targetAddressA, data)).to.be.revertedWithCustomError(
          roles,
          "FunctionSignatureTooShort",
        );
      }

      // Clearance.Target
      await roles.allowTargetPacked(
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      );
      for (const data of shortPayloads) {
        await expect(exec(targetAddressA, data)).to.be.revertedWithCustomError(
          roles,
          "FunctionSignatureTooShort",
        );
      }
    });

    it("does not match empty calldata to selector 0x00000000 under Clearance.Function", async () => {
      const { roles, targetA, targetAddressA, roleKey, exec, fundAvatar } =
        await loadFixture(setup);

      await roles.scopeTarget(roleKey, targetAddressA);
      await roles.allowFunctionPacked(
        roleKey,
        targetAddressA,
        "0x00000000",
        "0x",
        ExecutionOptions.Send,
      );
      await fundAvatar();

      // Explicit 4-byte 0x00000000 selector is allowed
      await expect(exec(targetAddressA, "0x00000000"))
        .to.emit(targetA, "Invoked")
        .withArgs("0x00000000");

      // Empty calldata must not match selector 0x00000000
      await expect(exec(targetAddressA, "0x"))
        .to.be.revertedWithCustomError(roles, "TransactionNotAllowed")
        .withArgs(targetAddressA, "0x00000000");

      // Empty calldata ETH transfer must also be rejected
      await expect(
        exec(targetAddressA, "0x", { value: ethers.parseEther("0.5") }),
      )
        .to.be.revertedWithCustomError(roles, "TransactionNotAllowed")
        .withArgs(targetAddressA, "0x00000000");
    });

    it("does not match empty calldata to global selector 0x00000000", async () => {
      const { roles, targetA, targetAddressA, roleKey, exec } =
        await loadFixture(setup);

      await roles.allowFunctionGloballyPacked(roleKey, "0x00000000", "0x");

      // Explicit 4-byte 0x00000000 selector resolves via global rule
      await expect(exec(targetAddressA, "0x00000000"))
        .to.emit(targetA, "Invoked")
        .withArgs("0x00000000");

      // Empty calldata must skip global lookup
      await expect(exec(targetAddressA, "0x"))
        .to.be.revertedWithCustomError(roles, "TransactionNotAllowed")
        .withArgs(targetAddressA, "0x00000000");
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  // 2. SCOPE RESOLUTION & CLEARANCE STATE MACHINE
  // ═══════════════════════════════════════════════════════════════════════════

  describe("scope resolution", () => {
    describe("Clearance.None", () => {
      it("reverts with TransactionNotAllowed when no global rule exists", async () => {
        const { roles, targetAddressA, exec } = await loadFixture(setup);

        await expect(exec(targetAddressA, "0x"))
          .to.be.revertedWithCustomError(roles, "TransactionNotAllowed")
          .withArgs(targetAddressA, "0x00000000");

        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing")),
        )
          .to.be.revertedWithCustomError(roles, "TransactionNotAllowed")
          .withArgs(targetAddressA, DO_NOTHING);
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

        await roles.allowFunctionGloballyPacked(roleKey, DO_NOTHING, "0x");

        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing")),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(DO_NOTHING);

        await expect(
          exec(targetAddressB, iface.encodeFunctionData("doNothing")),
        )
          .to.emit(targetB, "Invoked")
          .withArgs(DO_NOTHING);
      });
    });

    describe("Clearance.Target", () => {
      it("allows any function on target", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.allowTargetPacked(
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        );

        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing")),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(DO_NOTHING);

        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(ONE_PARAM);
      });

      it("takes precedence over a looser global function entry", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        // Target-specific: first param must equal 42
        await roles.allowTargetPacked(
          roleKey,
          targetAddressA,
          await eqFirstParam(roles, 42),
          ExecutionOptions.None,
        );
        // Global: unconstrained
        await roles.allowFunctionGloballyPacked(roleKey, ONE_PARAM, "0x");

        // 42 passes via target entry
        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(ONE_PARAM);

        // 99 fails — target rule governs, does not fall through to global
        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [99]),
          ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });
    });

    describe("Clearance.Function", () => {
      it("allows only permitted selectors and reverts TransactionNotAllowed for others", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.scopeTarget(roleKey, targetAddressA);
        await roles.allowFunctionPacked(
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        );

        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing")),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(DO_NOTHING);

        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        )
          .to.be.revertedWithCustomError(roles, "TransactionNotAllowed")
          .withArgs(targetAddressA, ONE_PARAM);
      });

      it("takes precedence over a global function entry for the same selector", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        // Target-specific: param must equal 42
        await roles.scopeTarget(roleKey, targetAddressA);
        await roles.allowFunctionPacked(
          roleKey,
          targetAddressA,
          ONE_PARAM,
          await eqFirstParam(roles, 42),
          ExecutionOptions.None,
        );
        // Global: unconstrained
        await roles.allowFunctionGloballyPacked(roleKey, ONE_PARAM, "0x");

        // 42 passes via function rule
        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(ONE_PARAM);

        // 99 fails — target-specific function rule governs, not global
        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [99]),
          ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });

      it("falls back to global function entry when selector is not configured on target", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.scopeTarget(roleKey, targetAddressA);
        await roles.allowFunctionPacked(
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        );
        await roles.allowFunctionGloballyPacked(roleKey, ONE_PARAM, "0x");

        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(ONE_PARAM);
      });

      it("does not collide selector 0xffffffff with Target scope entry", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        const maxSelector = "0xffffffff";
        const payload = (n: number) =>
          maxSelector + abiCoder.encode(["uint256"], [n]).slice(2);

        // Target entry requires param == 100
        await roles.allowTargetPacked(
          roleKey,
          targetAddressA,
          await eqFirstParam(roles, 100),
          ExecutionOptions.None,
        );
        // Function entry for 0xffffffff requires param == 42 (must not clobber target entry)
        await roles.allowFunctionPacked(
          roleKey,
          targetAddressA,
          maxSelector,
          await eqFirstParam(roles, 42),
          ExecutionOptions.None,
        );

        // While Clearance.Target: target entry (100) governs
        await expect(exec(targetAddressA, payload(100)))
          .to.emit(targetA, "Invoked")
          .withArgs(maxSelector);
        await expect(
          exec(targetAddressA, payload(42)),
        ).to.be.revertedWithCustomError(roles, "ConditionViolation");

        // Switch to Clearance.Function: function entry (42) governs
        await roles.scopeTarget(roleKey, targetAddressA);
        await expect(exec(targetAddressA, payload(42)))
          .to.emit(targetA, "Invoked")
          .withArgs(maxSelector);
        await expect(
          exec(targetAddressA, payload(100)),
        ).to.be.revertedWithCustomError(roles, "ConditionViolation");
      });
    });

    describe("clearance state machine & entry independence", () => {
      it("Target -> Function: scopeTarget tightens previously allowed target", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.allowTargetPacked(
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        );
        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(ONE_PARAM);

        await roles.scopeTarget(roleKey, targetAddressA);
        await roles.allowFunctionPacked(
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        );

        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing")),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(DO_NOTHING);

        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        )
          .to.be.revertedWithCustomError(roles, "TransactionNotAllowed")
          .withArgs(targetAddressA, ONE_PARAM);
      });

      it("Function -> Target: allowTarget loosens previously scoped target", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.scopeTarget(roleKey, targetAddressA);
        await roles.allowFunctionPacked(
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        );

        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");

        await roles.allowTargetPacked(
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        );

        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(ONE_PARAM);
      });

      it("Function -> Target -> Function: prior function entries reactivate when re-scoped", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.scopeTarget(roleKey, targetAddressA);
        await roles.allowFunctionPacked(
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        );

        // Loosen to Target, then tighten back to Function without re-calling allowFunction
        await roles.allowTargetPacked(
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        );
        await roles.scopeTarget(roleKey, targetAddressA);

        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing")),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(DO_NOTHING);

        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");
      });

      it("Function -> None: revokeTarget disables function entries while leaving global fallback active", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.scopeTarget(roleKey, targetAddressA);
        await roles.allowFunctionPacked(
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        );
        await roles.allowFunctionGloballyPacked(roleKey, ONE_PARAM, "0x");

        await roles.revokeTarget(roleKey, targetAddressA);

        // Target-scoped doNothing is now disabled
        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing")),
        ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");

        // Global oneParamStatic still authorizes under Clearance.None
        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(ONE_PARAM);
      });

      it("Target -> None: revokeTarget disables target entry while leaving global fallback active", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.allowTargetPacked(
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        );
        await roles.allowFunctionGloballyPacked(roleKey, ONE_PARAM, "0x");

        await roles.revokeTarget(roleKey, targetAddressA);

        // Target-level doNothing is disabled
        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing")),
        ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");

        // Global oneParamStatic still authorizes
        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [42]),
          ),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(ONE_PARAM);
      });

      it("allowFunction written while Clearance.None stays dormant until scopeTarget", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        // Write function entry before scoping target
        await roles.allowFunctionPacked(
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        );

        // Dormant under Clearance.None
        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing")),
        ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");

        // Activates once scoped
        await roles.scopeTarget(roleKey, targetAddressA);
        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing")),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(DO_NOTHING);
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
        await roles.scopeTarget(roleKey, targetAddressA);
        await roles.allowFunctionPacked(
          roleKey,
          targetAddressA,
          ONE_PARAM,
          await eqFirstParam(roles, 42),
          ExecutionOptions.None,
        );
        await roles.allowFunctionGloballyPacked(roleKey, ONE_PARAM, "0x");

        await roles.revokeFunction(roleKey, targetAddressA, ONE_PARAM);

        // Target-specific constraint is gone — global fallback allows param == 99
        await expect(
          exec(
            targetAddressA,
            iface.encodeFunctionData("oneParamStatic", [99]),
          ),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(ONE_PARAM);

        // Global still works on other targets
        await expect(
          exec(
            targetAddressB,
            iface.encodeFunctionData("oneParamStatic", [99]),
          ),
        )
          .to.emit(targetB, "Invoked")
          .withArgs(ONE_PARAM);
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

        await roles.scopeTarget(roleKey, targetAddressA);
        await roles.allowFunctionPacked(
          roleKey,
          targetAddressA,
          DO_NOTHING,
          "0x",
          ExecutionOptions.None,
        );
        await roles.allowFunctionGloballyPacked(roleKey, DO_NOTHING, "0x");

        await roles.revokeFunctionGlobally(roleKey, DO_NOTHING);

        // Target-specific still works
        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing")),
        )
          .to.emit(targetA, "Invoked")
          .withArgs(DO_NOTHING);

        // Global no longer works on other targets
        await expect(
          exec(targetAddressB, iface.encodeFunctionData("doNothing")),
        ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");
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
        data: "0x",
        expectedSelector: "0x00000000",
        configure: async (
          roles: Roles,
          roleKey: string,
          target: string,
          options: ExecutionOptions,
        ) => {
          await roles.allowTargetPacked(roleKey, target, "0x", options);
        },
      },
      {
        label: "Clearance.Function",
        data: iface.encodeFunctionData("doNothing"),
        expectedSelector: DO_NOTHING,
        configure: async (
          roles: Roles,
          roleKey: string,
          target: string,
          options: ExecutionOptions,
        ) => {
          await roles.scopeTarget(roleKey, target);
          await roles.allowFunctionPacked(
            roleKey,
            target,
            DO_NOTHING,
            "0x",
            options,
          );
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

          await expect(exec(targetAddressA, scope.data))
            .to.emit(targetA, "Invoked")
            .withArgs(scope.expectedSelector);

          await expect(
            exec(targetAddressA, scope.data, {
              value: ethers.parseEther("0.1"),
            }),
          )
            .to.be.revertedWithCustomError(roles, "SendNotAllowed")
            .withArgs(targetAddressA);

          await expect(exec(targetAddressA, scope.data, { operation: 1 }))
            .to.be.revertedWithCustomError(roles, "DelegateCallNotAllowed")
            .withArgs(targetAddressA);
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

          const amount = ethers.parseEther("0.1");
          await expect(
            exec(targetAddressA, scope.data, { value: amount }),
          ).to.changeEtherBalances(
            ethers,
            [avatarAddress, targetAddressA],
            [-amount, amount],
          );

          await expect(exec(targetAddressA, scope.data, { operation: 1 }))
            .to.be.revertedWithCustomError(roles, "DelegateCallNotAllowed")
            .withArgs(targetAddressA);

          // Verify zero-value Call also still works
          await expect(exec(targetAddressA, scope.data))
            .to.emit(targetA, "Invoked")
            .withArgs(scope.expectedSelector);
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
          await expect(exec(targetAddressA, scope.data, { operation: 1 }))
            .to.emit(targetA.attach(avatarAddress), "Invoked")
            .withArgs(scope.expectedSelector);

          // Regular Call with 0 value still works
          await expect(exec(targetAddressA, scope.data))
            .to.emit(targetA, "Invoked")
            .withArgs(scope.expectedSelector);

          // Sending ETH value is still blocked
          await expect(
            exec(targetAddressA, scope.data, {
              value: ethers.parseEther("0.1"),
            }),
          )
            .to.be.revertedWithCustomError(roles, "SendNotAllowed")
            .withArgs(targetAddressA);
        });

        it("Both: allows Send, DelegateCall, and both together", async () => {
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
            ExecutionOptions.Both,
          );
          await fundAvatar();

          const amount = ethers.parseEther("0.1");
          await expect(
            exec(targetAddressA, scope.data, { value: amount }),
          ).to.changeEtherBalances(
            ethers,
            [avatarAddress, targetAddressA],
            [-amount, amount],
          );

          await expect(exec(targetAddressA, scope.data, { operation: 1 }))
            .to.emit(targetA.attach(avatarAddress), "Invoked")
            .withArgs(scope.expectedSelector);

          // Combined value > 0 and DelegateCall passes both option checks
          await expect(
            exec(targetAddressA, scope.data, { value: amount, operation: 1 }),
          )
            .to.emit(targetA.attach(avatarAddress), "Invoked")
            .withArgs(scope.expectedSelector);
        });
      });
    }

    describe("global function entry", () => {
      it("always blocks Send and DelegateCall while allowing Call(0)", async () => {
        const { roles, targetA, targetAddressA, roleKey, exec, fundAvatar } =
          await loadFixture(setup);

        await roles.allowFunctionGloballyPacked(roleKey, DO_NOTHING, "0x");
        await fundAvatar();

        const data = iface.encodeFunctionData("doNothing");

        await expect(exec(targetAddressA, data, { value: 1n }))
          .to.be.revertedWithCustomError(roles, "SendNotAllowed")
          .withArgs(targetAddressA);

        await expect(exec(targetAddressA, data, { operation: 1 }))
          .to.be.revertedWithCustomError(roles, "DelegateCallNotAllowed")
          .withArgs(targetAddressA);

        await expect(exec(targetAddressA, data))
          .to.emit(targetA, "Invoked")
          .withArgs(DO_NOTHING);
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

      await roles.allowTargetPacked(
        roleKey,
        targetAddressA,
        await eqFirstParam(roles, 100),
        ExecutionOptions.None,
      );

      await expect(
        exec(targetAddressA, iface.encodeFunctionData("oneParamStatic", [100])),
      )
        .to.emit(targetA, "Invoked")
        .withArgs(ONE_PARAM);

      await expect(
        exec(targetAddressA, iface.encodeFunctionData("oneParamStatic", [50])),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);

      await expect(
        exec(
          targetAddressA,
          iface.encodeFunctionData("twoParamsStatic", [100, 999]),
        ),
      ).to.not.be.revert(ethers);

      await expect(
        exec(
          targetAddressA,
          iface.encodeFunctionData("twoParamsStatic", [200, 999]),
        ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("evaluates function-specific conditions", async () => {
      const { roles, targetA, targetAddressA, roleKey, exec } =
        await loadFixture(setup);

      await roles.scopeTarget(roleKey, targetAddressA);
      await roles.allowFunctionPacked(
        roleKey,
        targetAddressA,
        ONE_PARAM,
        await eqFirstParam(roles, 42),
        ExecutionOptions.None,
      );

      await expect(
        exec(targetAddressA, iface.encodeFunctionData("oneParamStatic", [42])),
      )
        .to.emit(targetA, "Invoked")
        .withArgs(ONE_PARAM);

      await expect(
        exec(targetAddressA, iface.encodeFunctionData("oneParamStatic", [99])),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("evaluates global function conditions", async () => {
      const { roles, targetA, targetAddressA, roleKey, exec } =
        await loadFixture(setup);

      await roles.allowFunctionGloballyPacked(
        roleKey,
        ONE_PARAM,
        await eqFirstParam(roles, 100),
      );

      await expect(
        exec(targetAddressA, iface.encodeFunctionData("oneParamStatic", [100])),
      )
        .to.emit(targetA, "Invoked")
        .withArgs(ONE_PARAM);

      await expect(
        exec(targetAddressA, iface.encodeFunctionData("oneParamStatic", [50])),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    describe("check ordering", () => {
      it("reverts SendNotAllowed before DelegateCallNotAllowed when both are disallowed", async () => {
        const { roles, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.allowTargetPacked(
          roleKey,
          targetAddressA,
          "0x",
          ExecutionOptions.None,
        );

        await expect(
          exec(targetAddressA, iface.encodeFunctionData("doNothing"), {
            value: 1n,
            operation: 1,
          }),
        )
          .to.be.revertedWithCustomError(roles, "SendNotAllowed")
          .withArgs(targetAddressA);
      });

      it("enforces ExecutionOptions before evaluating conditions", async () => {
        const { roles, targetAddressA, roleKey, exec } =
          await loadFixture(setup);

        await roles.allowTargetPacked(
          roleKey,
          targetAddressA,
          await eqFirstParam(roles, 42),
          ExecutionOptions.None,
        );

        const violatingData = iface.encodeFunctionData("oneParamStatic", [99]);

        await expect(exec(targetAddressA, violatingData, { value: 1n }))
          .to.be.revertedWithCustomError(roles, "SendNotAllowed")
          .withArgs(targetAddressA);

        await expect(exec(targetAddressA, violatingData, { operation: 1 }))
          .to.be.revertedWithCustomError(roles, "DelegateCallNotAllowed")
          .withArgs(targetAddressA);
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

      await roles.allowTargetPacked(
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      );

      const batchData = encodeBatch([
        {
          to: targetAddressA,
          value: 0,
          operation: 0,
          data: iface.encodeFunctionData("doNothing"),
        },
        {
          to: targetAddressA,
          value: 0,
          operation: 0,
          data: iface.encodeFunctionData("oneParamStatic", [42]),
        },
      ]);

      await expect(exec(multisendAddress, batchData, { operation: 1 }))
        .to.emit(targetA, "Invoked")
        .withArgs(DO_NOTHING)
        .and.to.emit(targetA, "Invoked")
        .withArgs(ONE_PARAM);
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

      await roles.allowTargetPacked(
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      );

      // Register unwrappers for selectors with trailing zero bytes
      for (const selector of [
        "0x00000000",
        "0x12000000",
        "0x12340000",
        "0x12345600",
      ]) {
        await roles.setTransactionUnwrapper(
          targetAddressA,
          selector,
          unwrapperAddress,
        );
      }

      // 0 bytes bypasses unwrapper lookup and succeeds under Clearance.Target
      await expect(exec(targetAddressA, "0x"))
        .to.emit(targetA, "Invoked")
        .withArgs("0x00000000");

      // 1-3 bytes bypass unwrapper lookup and revert FunctionSignatureTooShort
      for (const shortData of ["0x12", "0x1234", "0x123456"]) {
        await expect(
          exec(targetAddressA, shortData),
        ).to.be.revertedWithCustomError(roles, "FunctionSignatureTooShort");
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

      await roles.allowTargetPacked(
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      );
      await fundAvatar();

      // Empty multisend payload
      const emptyPayload = multisend.interface.encodeFunctionData("multiSend", [
        "0x",
      ]);
      await expect(
        exec(multisendAddress, emptyPayload, { operation: 1 }),
      ).to.be.revertedWithCustomError(roles, "MalformedMultiEntrypoint");

      const validBatch = encodeBatch([
        {
          to: targetAddressA,
          value: 0,
          operation: 0,
          data: iface.encodeFunctionData("doNothing"),
        },
      ]);

      // Outer Call instead of DelegateCall
      await expect(
        exec(multisendAddress, validBatch, { operation: 0 }),
      ).to.be.revertedWithCustomError(roles, "MalformedMultiEntrypoint");

      // Non-zero outer ETH value
      await expect(
        exec(multisendAddress, validBatch, { value: 1n, operation: 1 }),
      ).to.be.revertedWithCustomError(roles, "MalformedMultiEntrypoint");
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

      await roles.scopeTarget(roleKey, targetAddressA);
      await roles.allowFunctionPacked(
        roleKey,
        targetAddressA,
        ONE_PARAM,
        await eqFirstParam(roles, 42),
        ExecutionOptions.None,
      );
      await fundAvatar();

      const validEntry = {
        to: targetAddressA,
        value: 0,
        operation: 0,
        data: iface.encodeFunctionData("oneParamStatic", [42]),
      };

      // Unauthorized inner target
      await expect(
        exec(
          multisendAddress,
          encodeBatch([
            validEntry,
            {
              to: targetAddressB,
              value: 0,
              operation: 0,
              data: iface.encodeFunctionData("doNothing"),
            },
          ]),
          { operation: 1 },
        ),
      )
        .to.be.revertedWithCustomError(roles, "TransactionNotAllowed")
        .withArgs(targetAddressB, DO_NOTHING);

      // Disallowed inner value transfer
      await expect(
        exec(
          multisendAddress,
          encodeBatch([validEntry, { ...validEntry, value: 1 }]),
          { operation: 1 },
        ),
      )
        .to.be.revertedWithCustomError(roles, "SendNotAllowed")
        .withArgs(targetAddressA);

      // Disallowed inner DelegateCall
      await expect(
        exec(
          multisendAddress,
          encodeBatch([validEntry, { ...validEntry, operation: 1 }]),
          { operation: 1 },
        ),
      )
        .to.be.revertedWithCustomError(roles, "DelegateCallNotAllowed")
        .withArgs(targetAddressA);

      // Inner condition violation
      await expect(
        exec(
          multisendAddress,
          encodeBatch([
            validEntry,
            {
              to: targetAddressA,
              value: 0,
              operation: 0,
              data: iface.encodeFunctionData("oneParamStatic", [99]),
            },
          ]),
          { operation: 1 },
        ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);

      // Inner short calldata (1-3 bytes)
      await expect(
        exec(
          multisendAddress,
          encodeBatch([
            validEntry,
            { to: targetAddressA, value: 0, operation: 0, data: "0x1234" },
          ]),
          { operation: 1 },
        ),
      ).to.be.revertedWithCustomError(roles, "FunctionSignatureTooShort");
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

      const ALLOWANCE_KEY = ethers.id("BATCH_ALLOWANCE");
      await roles.setAllowance(ALLOWANCE_KEY, 1000, 0, 0, 0, 0);

      await roles.scopeTarget(roleKey, targetAddressA);
      await roles.allowFunctionPacked(
        roleKey,
        targetAddressA,
        ONE_PARAM,
        await withinAllowanceFirstParam(roles, ALLOWANCE_KEY),
        ExecutionOptions.None,
      );

      // 100 + 200 = 300 <= 1000 succeeds and settles to 700
      const okBatch = encodeBatch([
        {
          to: targetAddressA,
          value: 0,
          operation: 0,
          data: iface.encodeFunctionData("oneParamStatic", [100]),
        },
        {
          to: targetAddressA,
          value: 0,
          operation: 0,
          data: iface.encodeFunctionData("oneParamStatic", [200]),
        },
      ]);
      await expect(exec(multisendAddress, okBatch, { operation: 1 }))
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(ALLOWANCE_KEY, 300, 700);

      // 400 + 400 = 800 > 700 rejects on the second entry before execution
      const overflowBatch = encodeBatch([
        {
          to: targetAddressA,
          value: 0,
          operation: 0,
          data: iface.encodeFunctionData("oneParamStatic", [400]),
        },
        {
          to: targetAddressA,
          value: 0,
          operation: 0,
          data: iface.encodeFunctionData("oneParamStatic", [400]),
        },
      ]);
      await expect(exec(multisendAddress, overflowBatch, { operation: 1 }))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 1, anyValue);

      expect((await roles.accruedAllowance(ALLOWANCE_KEY)).balance).to.equal(
        700,
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

      await roles.allowTargetPacked(
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      );

      const innerBatch = encodeBatch([
        {
          to: targetAddressA,
          value: 0,
          operation: 0,
          data: iface.encodeFunctionData("doNothing"),
        },
      ]);
      const outerBatch = encodeBatch([
        {
          to: multisendAddress,
          value: 0,
          operation: 1,
          data: innerBatch,
        },
      ]);

      // Inner call to MultiSend is checked via _transaction, not unwrapped again
      await expect(exec(multisendAddress, outerBatch, { operation: 1 }))
        .to.be.revertedWithCustomError(roles, "TransactionNotAllowed")
        .withArgs(multisendAddress, multiSendSelector);
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

      await roles.allowTargetPacked(
        roleKey,
        targetAddressA,
        "0x",
        ExecutionOptions.None,
      );

      // Remove unwrapper
      await roles.setTransactionUnwrapper(
        multisendAddress,
        multiSendSelector,
        ZeroAddress,
      );

      const batchData = encodeBatch([
        {
          to: targetAddressA,
          value: 0,
          operation: 0,
          data: iface.encodeFunctionData("doNothing"),
        },
      ]);

      // Now goes directly through _transaction, where MultiSend has Clearance.None
      await expect(exec(multisendAddress, batchData, { operation: 1 }))
        .to.be.revertedWithCustomError(roles, "TransactionNotAllowed")
        .withArgs(multisendAddress, multiSendSelector);
    });
  });
});
