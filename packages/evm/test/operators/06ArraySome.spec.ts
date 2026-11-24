import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import { network } from "hardhat";
import { encodeAbiParameters, parseAbiParameters, toHex } from "viem";

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
const { setupTestContract, setupFn } = createSetup(connection);
const setupArrayParam = setupFn("function fn(uint256[])");

describe("Operator - ArraySome", () => {
  after(async () => {
    await connection.close();
  });

  describe("element matching", () => {
    it("passes when at least one element matches", async () => {
      const { allowFunction, invoke } = await loadFixture(setupArrayParam);

      // ArraySome: at least one element must equal 42
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArraySome,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [42n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Array with matching element passes
      await invoke([1, 2, 42, 4]);

      // Array with only matching element passes
      await invoke([42]);
    });

    it("fails when no element matches", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      // ArraySome: at least one element must equal 42
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArraySome,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [42n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Array with no matching element fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([1, 2, 3, 4]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NoArrayElementPasses,
          1n, // ArraySome node
          anyValue,
        ],
      );
    });

    it("fails when array is empty", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      // ArraySome: at least one element must equal 42
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArraySome,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [42n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Empty array fails - no element can match
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NoArrayElementPasses,
          1n, // ArraySome node
          anyValue,
        ],
      );
    });

    it("returns on first match (short-circuit)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      const allowanceKey =
        "0x000000000000000000000000000000000000000000000000000000000000abcd" as const;

      // Set up allowance of 100
      await roles.write.setAllowance([allowanceKey, 100n, 0n, 0n, 0n, 0n]);

      // ArraySome with WithinAllowance - consumes value of matching element
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArraySome,
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

      // Array [10, 20, 30] - first element (10) matches and is consumed
      // If not short-circuiting, all would be consumed (60 total)
      await invoke([10, 20, 30]);

      // Only 10 was consumed (first match), not 60 - remaining is 90
      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 90n);
    });
  });

  describe("consumption handling", () => {
    it("uses consumptions from matching element only", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      const allowanceKey =
        "0x000000000000000000000000000000000000000000000000000000000000abcd" as const;

      // Set up allowance of 50
      await roles.write.setAllowance([allowanceKey, 50n, 0n, 0n, 0n, 0n]);

      // ArraySome with And(GreaterThan(15), WithinAllowance)
      // Only elements > 15 can match, and matching consumes their value
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArraySome,
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.GreaterThan,
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [15n],
                      ),
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

      // Array [5, 10, 20, 30] - elements 5, 10 fail (<=15), element 20 matches
      // Only 20 is consumed (first matching element)
      await invoke([5, 10, 20, 30]);

      // Only 20 consumed from matching element - remaining is 30
      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 30n);
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
              operator: Operator.ArraySome,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [42n],
                  ),
                },
              ],
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([1, 2, 3]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NoArrayElementPasses,
          1n, // ArraySome node at BFS index 1
          anyValue,
        ],
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
              operator: Operator.ArraySome,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [42n],
                  ),
                },
              ],
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([1, 2, 3]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NoArrayElementPasses,
          anyValue,
          36n, // calldataOffset: array data starts at byte 36
        ],
      );
    });
  });

  describe("integrity", () => {
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
        await viem.assertions.revertWithCustomError(
          allowTarget([
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.ArraySome,
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
            paramType: Encoding.Array,
            operator: Operator.ArraySome,
            compValue: "0x01",
          },
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
        evaluator,
        "UnsuitableCompValue",
      );
    });

    describe("children", () => {
      it("reverts UnsuitableChildCount when ArraySome has zero children", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        await viem.assertions.revertWithCustomError(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Array,
              operator: Operator.ArraySome,
              compValue: "0x",
            },
          ]),
          evaluator,
          "UnsuitableChildCount",
        );
      });

      it("reverts UnsuitableChildCount when ArraySome has more than one child", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        // ArraySome requires exactly 1 structural child
        await viem.assertions.revertWithCustomError(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Array,
              operator: Operator.ArraySome,
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
          evaluator,
          "UnsuitableChildCount",
        );

        // ArraySome requires exactly 1 structural child
        await viem.assertions.revertWithCustomError(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Array,
              operator: Operator.ArraySome,
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
          evaluator,
          "UnsuitableChildCount",
        );
      });

      it("reverts UnsuitableChildCount when ArraySome has non-structural child", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        const allowanceKey = toHex(randomBytes(32));

        // Valid: ArraySome with one structural child - should succeed
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
            operator: Operator.ArraySome,
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
        await viem.assertions.revertWithCustomError(
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
              operator: Operator.ArraySome,
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
          evaluator,
          "UnsuitableChildCount",
        );
      });
    });
  });
});
