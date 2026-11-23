import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { AbiCoder, hexlify, randomBytes } from "ethers";

import { network } from "hardhat";

import { createSetup } from "../setup.js";
import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
} from "../utils.js";

const abiCoder = AbiCoder.defaultAbiCoder();

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupArrayParam = setupFn("function fn(uint256[])");

describe("Operator - ArrayEvery", () => {
  after(async () => {
    await connection.close();
  });

  describe("element matching", () => {
    it("passes when all elements match", async () => {
      const { allowFunction, invoke } = await loadFixture(setupArrayParam);

      // ArrayEvery: all elements must be less than 100
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayEvery,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.LessThan,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // All elements < 100 passes
      await expect(invoke([10, 20, 30, 40])).to.not.be.revert(ethers);
    });

    it("fails when at least one element does not match", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      // ArrayEvery: all elements must be less than 100
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayEvery,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.LessThan,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // One element >= 100 fails
      await expect(invoke([10, 20, 150, 40]))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.NotEveryArrayElementPasses,
          2, // LessThan node (failing element's child)
          anyValue,
        );
    });

    it("fails immediately on first mismatch (short-circuit)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      const allowanceKey = hexlify(randomBytes(32));

      // Set up allowance of 100
      await roles.setAllowance(allowanceKey, 100, 0, 0, 0, 0);

      // ArrayEvery with And(LessThan(50), WithinAllowance)
      // Elements >= 50 fail before consuming allowance
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayEvery,
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.LessThan,
                      compValue: abiCoder.encode(["uint256"], [50]),
                    },
                    {
                      paramType: Encoding.Static,
                      operator: Operator.WithinAllowance,
                      compValue: allowanceKey,
                    },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Array [10, 60, 20] - first element (10) passes and consumes
      // Second element (60) fails LessThan check before WithinAllowance
      // Transaction reverts, but consumptions from element 0 are NOT persisted
      await expect(invoke([10, 60, 20]))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.NotEveryArrayElementPasses,
          3, // LessThan node (failing element's child)
          anyValue,
        );

      // Allowance unchanged - transaction reverted so no consumption persisted
      const { balance } = await roles.accruedAllowance(allowanceKey);
      expect(balance).to.equal(100);
    });

    it("passes when array is empty (vacuous truth)", async () => {
      const { allowFunction, invoke } = await loadFixture(setupArrayParam);

      // ArrayEvery: all elements must equal 42
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayEvery,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Empty array passes - no element violates the condition (vacuous truth)
      await expect(invoke([])).to.not.be.revert(ethers);
    });
  });

  describe("consumption handling", () => {
    it("accumulates consumptions from all elements", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      const allowanceKey =
        "0x000000000000000000000000000000000000000000000000000000000000abcd";

      // Set up allowance of 100
      await roles.setAllowance(allowanceKey, 100, 0, 0, 0, 0);

      // ArrayEvery with WithinAllowance - each element consumes its value
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayEvery,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.WithinAllowance,
                  compValue: allowanceKey,
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Array [10, 20, 30] - all elements pass, all consumed (60 total)
      await expect(invoke([10, 20, 30])).to.not.be.revert(ethers);

      // All elements consumed - remaining is 40
      const { balance } = await roles.accruedAllowance(allowanceKey);
      expect(balance).to.equal(40);
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayEvery,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
              ],
            },
          ],
        }),
      );

      await expect(invoke([42, 99, 42]))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.NotEveryArrayElementPasses,
          2, // EqualTo node at BFS index 2
          anyValue,
        );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayEvery,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
              ],
            },
          ],
        }),
      );

      await expect(invoke([1, 2, 3]))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.NotEveryArrayElementPasses,
          anyValue,
          68, // calldataOffset: first element at byte 68 (4 + 32 + 32)
        );
    });
  });

  describe("integrity", () => {
    describe("encoding", () => {
      it("reverts UnsuitableParameterType for invalid encodings", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        for (const encoding of [
          Encoding.AbiEncoded,
          Encoding.Dynamic,
          Encoding.EtherValue,
          Encoding.None,
          Encoding.Static,
          Encoding.Tuple,
        ]) {
          await expect(
            allowTarget([
              {
                parent: 0,
                paramType: encoding,
                operator: Operator.ArrayEvery,
                compValue: "0x",
              },
            ]),
          ).to.be.revertedWithCustomError(evaluator, "UnsuitableParameterType");
        }
      });
    });

    it("reverts UnsuitableCompValue when compValue is not empty", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      await expect(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.Array,
            operator: Operator.ArrayEvery,
            compValue: "0x01",
          },
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
    });

    describe("children", () => {
      it("reverts UnsuitableChildCount when ArrayEvery has zero children", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Array,
              operator: Operator.ArrayEvery,
              compValue: "0x",
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableChildCount");
      });

      it("reverts UnsuitableChildCount when ArrayEvery has more than one child", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        // ArrayEvery requires exactly 1 structural child
        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Array,
              operator: Operator.ArrayEvery,
              compValue: "0x",
            },
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            },
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableChildCount");

        // ArrayEvery requires exactly 1 structural child
        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Array,
              operator: Operator.ArrayEvery,
              compValue: "0x",
            },
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            },
            {
              parent: 0,
              paramType: Encoding.None,
              operator: Operator.Pass,
              compValue: "0x",
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableChildCount");
      });

      it("reverts UnsuitableChildCount when ArrayEvery has non-structural child", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        const allowanceKey = hexlify(randomBytes(32));

        // Valid: ArrayEvery with one structural child - should succeed
        await allowTarget([
          {
            parent: 0,
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            compValue: "0x",
          },
          {
            parent: 0,
            paramType: Encoding.Array,
            operator: Operator.ArrayEvery,
            compValue: "0x",
          },
          {
            parent: 1,
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]);

        // Invalid: Adding a non-structural child should fail
        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x",
            },
            {
              parent: 0,
              paramType: Encoding.Array,
              operator: Operator.ArrayEvery,
              compValue: "0x",
            },
            {
              parent: 1,
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            },
            {
              parent: 1,
              paramType: Encoding.None,
              operator: Operator.CallWithinAllowance,
              compValue: allowanceKey,
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableChildCount");
      });
    });
  });
});
