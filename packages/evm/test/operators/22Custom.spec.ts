import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import {
  encodeFunctionData,
  maxUint256,
  toFunctionSelector,
  toHex,
} from "viem";

import { network } from "hardhat";

import { createSetup } from "../setup.js";
import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
} from "../utils.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupFn, setupTestContract } = createSetup(connection);
const setupOneParam = setupFn("function fn(uint256)");

describe("Operator - Custom", () => {
  after(async () => {
    await connection.close();
  });

  async function setupWithChecker() {
    const base = await setupOneParam();
    const customChecker = await viem.deployContract("TestCustomChecker");
    return {
      ...base,
      customChecker,
      customCheckerAddress: customChecker.address,
    };
  }

  describe("execution logic", () => {
    it("delegates execution to the configured adapter address", async () => {
      const { allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      // Custom condition: param > 100
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 101 > 100 passes
      await invoke(101n);
    });

    it("passes correct context (operation type) to adapter", async () => {
      const {
        roles,
        member,
        testContractAddress,
        fn,
        allowFunction,
        customCheckerAddress,
      } = await loadFixture(setupWithChecker);

      // Adapter fails if operation != Call (0)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Call operation (0) passes
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi: [fn],
            functionName: fn.name,
            args: [101n],
          }),
          0, // Operation.Call
        ],
        { account: member.account },
      );

      // DelegateCall operation (1) fails (adapter returns false)
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi: [fn],
              functionName: fn.name,
              args: [101n],
            }),
            1, // Operation.DelegateCall
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CustomConditionViolation,
          1n, // Custom node
          anyValue,
        ],
      );
    });

    it("extracts and passes extra data (from compValue) to adapter", async () => {
      const { roles, allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      const extraData = "aabbccddeeff112233445566";
      const compValue = customCheckerAddress + extraData;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Fail condition: param <= 100.
      // Adapter should return false + extraData as error info.
      // Note: returned info is bytes32, so extraData is padded/truncated to 32 bytes
      const expectedInfo = "0x" + extraData.padEnd(64, "0");

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(99n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CustomConditionViolation,
          1n, // Custom node
          anyValue,
        ],
      );
    });
  });

  describe("result handling", () => {
    it("passes when adapter returns true", async () => {
      const { allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Adapter returns true for > 100
      await invoke(101n);
    });

    it("fails when adapter returns false (propagates error info)", async () => {
      const { roles, allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      const extraData = "1234"; // "reason" code
      const compValue = customCheckerAddress + extraData;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Adapter returns false for <= 100, info = extraData
      const expectedInfo = "0x" + extraData.padEnd(64, "0");

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(99n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CustomConditionViolation,
          1n, // Custom node
          anyValue,
        ],
      );
    });

    it("runs on None, with no operand to read", async () => {
      const { roles, allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);
      const passing = await viem.deployContract("TestCustomCheckerConsuming");

      const allowWith = (adapter: string) =>
        allowFunction(
          flattenCondition({
            paramType: Encoding.None,
            operator: Operator.And,
            children: [
              {
                paramType: Encoding.AbiEncoded,
                operator: Operator.Matches,
                children: [{ paramType: Encoding.Static }],
              },
              {
                paramType: Encoding.None,
                operator: Operator.Custom,
                compValue: adapter,
              },
            ],
          }),
          ExecutionOptions.Both,
        );

      // an adapter that passes without reading the operand
      await allowWith(passing.address);
      await invoke(101n);

      // an adapter that reads the operand sees none (size 0), whatever the
      // calldata holds, and fails
      await allowWith(customCheckerAddress);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(101n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.CustomConditionViolation, 2n, anyValue],
      );
    });

    it("is the whole condition of a target, on None", async () => {
      const { roles, member, testContractAddress, allowTarget } =
        await loadFixture(setupTestContract);
      const passing = await viem.deployContract("TestCustomCheckerConsuming");
      const failing = await viem.deployContract("TestCustomChecker");

      const exec = () =>
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, toFunctionSelector("pause()"), 0],
          { account: member.account },
        );

      await allowTarget(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Custom,
          compValue: passing.address,
        }),
        ExecutionOptions.Both,
      );
      await exec();

      await allowTarget(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Custom,
          compValue: failing.address,
        }),
        ExecutionOptions.Both,
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec(),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.CustomConditionViolation, 0n, anyValue],
      );
    });
  });

  describe("adapter call safety", () => {
    it("no code at address: reverts", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupWithChecker);

      const randomAddress = toHex(randomBytes(20));
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: randomAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(101n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CustomConditionNotAContract,
          1n, // Custom node
          anyValue,
        ],
      );
    });

    it("wrong interface: reverts", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupWithChecker);

      // Deploy contract with code but no check() function and no fallback
      const noInterfaceChecker = await viem.deployContract(
        "TestCustomCheckerNoInterface",
      );
      const noInterfaceCheckerAddress = noInterfaceChecker.address;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: noInterfaceCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Function selector not found, no fallback -> staticcall fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(101n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CustomConditionReverted,
          1n, // Custom node
          anyValue,
        ],
      );
    });

    it("function reverts: reverts", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupWithChecker);

      const revertingChecker = await viem.deployContract(
        "TestCustomCheckerReverting",
      );
      const revertingCheckerAddress = revertingChecker.address;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: revertingCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Adapter reverts -> staticcall fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(101n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CustomConditionReverted,
          1n, // Custom node
          anyValue,
        ],
      );
    });

    it("returns wrong type: reverts", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupWithChecker);

      // Deploy contract that returns (uint256, uint256) instead of bool
      const wrongReturnChecker = await viem.deployContract(
        "TestCustomCheckerWrongReturn",
      );
      const wrongReturnCheckerAddress = wrongReturnChecker.address;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: wrongReturnCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Return data does not decode as (bool, AllowanceConsumption[])
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(101n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CustomConditionInvalidResult,
          1n, // Custom node
          anyValue,
        ],
      );
    });

    it("returns expected: succeeds", async () => {
      const { allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Valid adapter returns true -> passes
      await invoke(101n);
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
      );

      // Value <= 100 triggers custom checker failure
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(50n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CustomConditionViolation,
          1n, // Custom node at BFS index 1
          anyValue,
        ],
      );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(50n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CustomConditionViolation,
          anyValue,
          4n, // calldataOffset: parameter starts at byte 4
        ],
      );
    });
  });

  describe("allowance consumption", () => {
    const allowanceKeyA = `0x${"11".repeat(32)}` as const;
    const allowanceKeyB = `0x${"22".repeat(32)}` as const;

    async function setupConsuming() {
      const base = await setupOneParam();
      const consuming = await viem.deployContract("TestCustomCheckerConsuming");
      return {
        ...base,
        consumingAddress: consuming.address,
      };
    }

    const customCompValue = (adapter: string, ...keys: string[]) =>
      adapter + keys.map((key) => key.slice(2)).join("");

    const customCondition = (compValue: string) =>
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.Custom,
            compValue,
          },
        ],
      });

    it("consumes across calls and enforces the accrued balance", async () => {
      const { owner, roles, allowFunction, invoke, consumingAddress } =
        await loadFixture(setupConsuming);
      const compValue = customCompValue(consumingAddress, allowanceKeyA);

      await roles.write.setAllowance([allowanceKeyA, 100n, 0n, 0n, 0n, 0n], {
        account: owner.account,
      });
      await allowFunction(customCondition(compValue), ExecutionOptions.Both);

      await invoke(40n);
      assert.equal(
        (await roles.read.accruedAllowance([allowanceKeyA]))[0],
        60n,
      );

      // Exact remaining balance is allowed.
      await invoke(60n);
      assert.equal((await roles.read.accruedAllowance([allowanceKeyA]))[0], 0n);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 1n, anyValue],
      );
      assert.equal((await roles.read.accruedAllowance([allowanceKeyA]))[0], 0n);
    });

    it("checks pending consumption before loading from storage", async () => {
      const { owner, roles, allowFunction, invoke, consumingAddress } =
        await loadFixture(setupConsuming);
      const compValue = customCompValue(consumingAddress, allowanceKeyA);

      await roles.write.setAllowance([allowanceKeyA, 100n, 0n, 0n, 0n, 0n], {
        account: owner.account,
      });
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.WithinAllowance,
                  compValue: allowanceKeyA,
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.Custom,
                  compValue,
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Both checks charge 40 from the same running list.
      await invoke(40n);
      assert.equal(
        (await roles.read.accruedAllowance([allowanceKeyA]))[0],
        20n,
      );

      // 11 + 11 exceeds the 20 remaining. Loading storage independently in
      // each checker would incorrectly allow this call.
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(11n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 3n, anyValue],
      );
      assert.equal(
        (await roles.read.accruedAllowance([allowanceKeyA]))[0],
        20n,
      );
    });

    it("applies multiple consumptions and aggregates duplicate keys", async () => {
      const { owner, roles, allowFunction, invoke, consumingAddress } =
        await loadFixture(setupConsuming);

      await roles.write.setAllowance([allowanceKeyA, 100n, 0n, 0n, 0n, 0n], {
        account: owner.account,
      });
      await roles.write.setAllowance([allowanceKeyB, 100n, 0n, 0n, 0n, 0n], {
        account: owner.account,
      });
      await allowFunction(
        customCondition(
          customCompValue(consumingAddress, allowanceKeyA, allowanceKeyB),
        ),
        ExecutionOptions.Both,
      );

      await invoke(30n);
      assert.equal(
        (await roles.read.accruedAllowance([allowanceKeyA]))[0],
        70n,
      );
      assert.equal(
        (await roles.read.accruedAllowance([allowanceKeyB]))[0],
        70n,
      );

      // The same key twice must aggregate to 120 and fail atomically.
      await allowFunction(
        customCondition(
          customCompValue(consumingAddress, allowanceKeyA, allowanceKeyA),
        ),
        ExecutionOptions.Both,
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(60n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 1n, anyValue],
      );
      assert.equal(
        (await roles.read.accruedAllowance([allowanceKeyA]))[0],
        70n,
      );
    });

    it("does not leak partial consumptions from a discarded OR branch", async () => {
      const { owner, roles, allowFunction, invoke, consumingAddress } =
        await loadFixture(setupConsuming);
      const duplicate = customCompValue(
        consumingAddress,
        allowanceKeyA,
        allowanceKeyA,
      );

      await roles.write.setAllowance([allowanceKeyA, 100n, 0n, 0n, 0n, 0n], {
        account: owner.account,
      });
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.Or,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Custom,
                  compValue: duplicate,
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.Pass,
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // The first branch consumes 60 then fails on its second consumption. The
      // Pass branch succeeds, but no partial consumption may be settled.
      await invoke(60n);
      assert.equal(
        (await roles.read.accruedAllowance([allowanceKeyA]))[0],
        100n,
      );
    });

    it("handles arbitrary uint256 amounts without an arithmetic panic", async () => {
      const { owner, roles, allowFunction, invoke, consumingAddress } =
        await loadFixture(setupConsuming);
      const compValue = customCompValue(consumingAddress, allowanceKeyA);

      await roles.write.setAllowance([allowanceKeyA, 100n, 0n, 0n, 0n, 0n], {
        account: owner.account,
      });
      await allowFunction(customCondition(compValue), ExecutionOptions.Both);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(maxUint256),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 1n, anyValue],
      );
    });
  });

  describe("rich result validation", () => {
    it("rejects malformed results with a structured status", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);
      const malformed = await viem.deployContract("TestCustomCheckerMalformed");
      const adapter = malformed.address;

      for (const mode of ["00", "01", "02"]) {
        await allowFunction(
          customConditionForAdapter(adapter + mode),
          ExecutionOptions.Both,
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(101n),
          roles,
          "ConditionViolation",
          [ConditionViolationStatus.CustomConditionInvalidResult, 1n, anyValue],
        );
      }
    });
  });

  function customConditionForAdapter(compValue: string) {
    return flattenCondition({
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Static,
          operator: Operator.Custom,
          compValue,
        },
      ],
    });
  }
});
