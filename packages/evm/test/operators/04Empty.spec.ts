import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";

import { network } from "hardhat";

import { createSetup } from "../setup.js";
import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
} from "../utils.js";
import type { ConditionFlatStruct } from "../../typechain-types/contracts/Roles.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
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
      conditions: ConditionFlatStruct[],
      options = ExecutionOptions.None,
    ) => roles.allowTarget(roleKey, testContractAddress, conditions, options);

    const invoke = (
      data: string,
      options?: { value?: bigint | number; operation?: number },
    ) =>
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          options?.value ?? 0,
          data,
          options?.operation ?? 0,
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

      await expect(invoke("0x")).to.not.be.revert(ethers);
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

      await expect(invoke("0xdeadbeef"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CalldataNotEmpty,
          0, // Empty node
          anyValue,
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

      await expect(invoke("0xdeadbeef"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CalldataNotEmpty,
          0, // Empty node at BFS index 0
          anyValue,
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

      await expect(invoke("0xdeadbeef"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CalldataNotEmpty,
          anyValue,
          0, // calldataOffset: Empty checks entire calldata
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
        await expect(
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
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableParameterType");
      }
    });

    it("reverts UnsuitableCompValue when compValue is not empty", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      await expect(
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
      ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
    });

    it("reverts LeafNodeCannotHaveChildren when Empty has children", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      await expect(
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
      ).to.be.revertedWithCustomError(evaluator, "LeafNodeCannotHaveChildren");
    });
  });
});
