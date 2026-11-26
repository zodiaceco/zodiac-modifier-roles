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
const { setupFn } = createSetup(connection);
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

      // All elements < 100 passes
      await invoke([10, 20, 30, 40]);
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

      // One element >= 100 fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([10, 20, 150, 40]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryArrayElementPasses,
          2n, // LessThan node (failing element's child)
          anyValue,
        ],
      );
    });

    it("fails immediately on first mismatch (short-circuit)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      const allowanceKey = toHex(randomBytes(32));

      // Set up allowance of 100
      await roles.write.setAllowance([allowanceKey, 100n, 0n, 0n, 0n, 0n]);

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
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [50n],
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

      // Array [10, 60, 20] - first element (10) passes and consumes
      // Second element (60) fails LessThan check before WithinAllowance
      // Transaction reverts, but consumptions from element 0 are NOT persisted
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([10, 60, 20]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryArrayElementPasses,
          3n, // LessThan node (failing element's child)
          anyValue,
        ],
      );

      // Allowance unchanged - transaction reverted so no consumption persisted
      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 100n);
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

      // Empty array passes - no element violates the condition (vacuous truth)
      await invoke([]);
    });
  });

  describe("consumption handling", () => {
    it("accumulates consumptions from all elements", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupArrayParam);

      const allowanceKey =
        "0x000000000000000000000000000000000000000000000000000000000000abcd" as const;

      // Set up allowance of 100
      await roles.write.setAllowance([allowanceKey, 100n, 0n, 0n, 0n, 0n]);

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
      await invoke([10, 20, 30]);

      // All elements consumed - remaining is 40
      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 40n);
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
        invoke([42, 99, 42]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryArrayElementPasses,
          2n, // EqualTo node at BFS index 2
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
              operator: Operator.ArrayEvery,
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
          ConditionViolationStatus.NotEveryArrayElementPasses,
          anyValue,
          68n, // calldataOffset: first element at byte 68 (4 + 32 + 32)
        ],
      );
    });
  });
});
