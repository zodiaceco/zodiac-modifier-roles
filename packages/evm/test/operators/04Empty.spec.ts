import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import { network } from "hardhat";
import type { Hex } from "viem";

import { createSetup } from "../setup.js";
import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
  type ConditionFlat,
} from "../utils.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract } = createSetup(connection);

describe("Operator - Empty", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const { roles, member, testContractAddress, roleKey } =
      await setupTestContract();

    const allowTarget = async (
      conditions: ConditionFlat[],
      options = ExecutionOptions.None,
    ) =>
      roles.write.allowTarget([
        roleKey,
        testContractAddress,
        conditions,
        options,
      ]);

    const invoke = (
      data: Hex,
      options?: { value?: bigint | number; operation?: number },
    ) =>
      roles.write.execTransactionFromModule(
        [
          testContractAddress,
          BigInt(options?.value ?? 0),
          data,
          options?.operation ?? 0,
        ],
        { account: member.account },
      );

    return { roles, allowTarget, invoke };
  }

  describe("core behavior", () => {
    it("passes when calldata is empty", async () => {
      const { allowTarget, invoke } = await loadFixture(setup);

      await allowTarget(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Empty,
        }),
        ExecutionOptions.Both,
      );

      await invoke("0x");
    });

    it("fails when calldata is not empty", async () => {
      const { roles, allowTarget, invoke } = await loadFixture(setup);

      await allowTarget(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Empty,
        }),
        ExecutionOptions.Both,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xdeadbeef"),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CalldataNotEmpty,
          0n, // Empty node
          anyValue,
        ],
      );
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, allowTarget, invoke } = await loadFixture(setup);

      await allowTarget(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Empty,
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xdeadbeef"),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CalldataNotEmpty,
          0n, // Empty node at BFS index 0
          anyValue,
        ],
      );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, allowTarget, invoke } = await loadFixture(setup);

      await allowTarget(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Empty,
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xdeadbeef"),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.CalldataNotEmpty,
          anyValue,
          0n, // calldataOffset: Empty checks entire calldata
        ],
      );
    });
  });

  describe("integrity", () => {
    it("reverts UnsuitableParameterType for invalid encodings", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      for (const encoding of [
        Encoding.Static,
        Encoding.Dynamic,
        Encoding.Tuple,
        Encoding.Array,
        Encoding.AbiEncoded,
        Encoding.EtherValue,
      ]) {
        await viem.assertions.revertWithCustomError(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.None,
              operator: Operator.Or,
              compValue: "0x",
            },
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.Empty,
              compValue: "0x",
            },
          ]),
          evaluator,
          "UnsuitableParameterType",
        );
      }
    });

    it("reverts UnsuitableCompValue when compValue is not empty", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      await viem.assertions.revertWithCustomError(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.Or,
            compValue: "0x",
          },
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.Empty,
            compValue: "0x01",
          },
        ]),
        evaluator,
        "UnsuitableCompValue",
      );
    });

    it("reverts LeafNodeCannotHaveChildren when Empty has children", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      await viem.assertions.revertWithCustomError(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.Or,
            compValue: "0x",
          },
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.Empty,
            compValue: "0x",
          },
          {
            parent: 1,
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
        evaluator,
        "LeafNodeCannotHaveChildren",
      );
    });
  });
});
