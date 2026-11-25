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

describe("Operator - ArrayTailMatches", () => {
  after(async () => {
    await connection.close();
  });

  describe("matching logic", () => {
    it("matches when tail elements align with conditions", async () => {
      const { allowFunction, invoke } = await loadFixture(setupArrayParam);

      // ArrayTailMatches: last 2 elements must be 100, 200
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayTailMatches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [100n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [200n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Exact tail match passes
      await invoke([100, 200]);

      // Longer array with matching tail passes
      await invoke([1, 2, 3, 100, 200]);
    });

    it("fails when tail elements do not match", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      // ArrayTailMatches: last 2 elements must be 100, 200
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayTailMatches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [100n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [200n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Last element wrong
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([100, 999]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          3n, // Second EqualTo (last tail element)
          anyValue,
        ],
      );

      // Second-to-last element wrong
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([999, 200]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          2n, // First EqualTo (second-to-last tail element)
          anyValue,
        ],
      );
    });

    it("fails when array length is less than number of conditions", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      // ArrayTailMatches: requires 2 tail elements
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayTailMatches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [100n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [200n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Only 1 element - not enough for 2 conditions
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([100]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAMatch,
          1n, // ArrayTailMatches node
          anyValue,
        ],
      );

      // Empty array
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAMatch,
          1n, // ArrayTailMatches node
          anyValue,
        ],
      );
    });

    it("ignores elements before the tail (prefix insensitive)", async () => {
      const { allowFunction, invoke } = await loadFixture(setupArrayParam);

      // ArrayTailMatches: only checks last element
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayTailMatches,
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

      // Any prefix values are ignored - only tail (42) matters
      await invoke([999, 888, 777, 42]);

      // Different prefix, same tail - still passes
      await invoke([1, 2, 3, 4, 5, 42]);
    });
  });

  describe("routing & consumption", () => {
    it("routes correct tail element to corresponding child condition", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      // ArrayTailMatches with 3 conditions: [>10, ==50, <100]
      // For array [a, b, c, d, e] with 3 conditions:
      // - condition[0] (>10) matches element[2] (c)
      // - condition[1] (==50) matches element[3] (d)
      // - condition[2] (<100) matches element[4] (e)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayTailMatches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.GreaterThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [10n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [50n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.LessThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [100n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Array [1, 2, 20, 50, 80] - tail is [20, 50, 80]
      // 20 > 10 ✓, 50 == 50 ✓, 80 < 100 ✓
      await invoke([1, 2, 20, 50, 80]);

      // Array [5, 50, 80] - swapped first condition value
      // 5 > 10 ✗ - fails on first tail element
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([5, 50, 80]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterLessThanAllowed,
          2n, // GreaterThan node
          anyValue,
        ],
      );

      // Array [20, 99, 80] - wrong middle element
      // 20 > 10 ✓, 99 == 50 ✗
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([20, 99, 80]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          3n, // EqualTo node
          anyValue,
        ],
      );

      // Array [20, 50, 150] - last element too big
      // 20 > 10 ✓, 50 == 50 ✓, 150 < 100 ✗
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([20, 50, 150]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterGreaterThanAllowed,
          4n, // LessThan node
          anyValue,
        ],
      );
    });

    it("accumulates consumptions from all tail matches", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      const allowanceKey = toHex(randomBytes(32));

      // Set up allowance of 100
      await roles.write.setAllowance([allowanceKey, 100n, 0n, 0n, 0n, 0n]);

      // ArrayTailMatches with 2 WithinAllowance conditions
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayTailMatches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.WithinAllowance,
                  compValue: allowanceKey,
                },
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

      // Array [999, 20, 30] - prefix ignored, tail [20, 30] consumed (50 total)
      await invoke([999, 20, 30]);

      // Both tail elements consumed - remaining is 50
      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 50n);
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
              operator: Operator.ArrayTailMatches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [100n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [200n],
                  ),
                },
              ],
            },
          ],
        }),
      );

      // Array too short for 2 conditions
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([100]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAMatch,
          1n, // ArrayTailMatches node at BFS index 1
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
              operator: Operator.ArrayTailMatches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [200n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [300n],
                  ),
                },
              ],
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([100, 200, 999]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          anyValue,
          132n, // calldataOffset: last element at byte 132
        ],
      );
    });
  });
});
