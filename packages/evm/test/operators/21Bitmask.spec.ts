import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import {
  concat,
  encodeAbiParameters,
  parseAbiParameters,
  type Hex,
} from "viem";

import { network } from "hardhat";

import { createSetup } from "../setup.js";
import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
  packConditions,
} from "../utils.js";

// Helper: compValue = [shift (2 bytes)][mask (N bytes)][expected (N bytes)]
function encodeCompValue(shift: number, mask: string, expected: string): Hex {
  if (mask.length !== expected.length) {
    throw new Error("mask and expected must have same length");
  }
  const shiftHex = shift.toString(16).padStart(4, "0");
  return `0x${shiftHex}${mask}${expected}`;
}

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupDynamicParam = setupFn("function fn(bytes)");

describe("Operator - Bitmask", () => {
  after(async () => {
    await connection.close();
  });

  describe("parsing and bounds", () => {
    it("extracts shift and derives mask length correctly", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // shift=3, mask=2 bytes -> reads bytes[3:5]
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Bitmask,
              compValue: encodeCompValue(3, "ffff", "aabb"),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // bytes[3:5] = 0xaabb -> passes
      await invoke("0x000000aabb");

      // bytes[3:5] = 0xccdd -> fails
      await viem.assertions.revertWithCustomError(
        invoke("0x000000ccdd"),
        roles,
        "ConditionViolation",
      );
    });

    it("fails with BitmaskOverflow when shift + length exceeds data size", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // 33-byte mask requires 33 bytes (crosses word boundary)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Bitmask,
              compValue: encodeCompValue(0, "ff".repeat(33), "ab".repeat(33)),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // 33 bytes -> passes
      await invoke("0x" + "ab".repeat(33));

      // 32 bytes -> fails (crosses into second word but data only has one word)
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x" + "ab".repeat(32)),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.BitmaskOverflow, 1n, anyValue],
      );
    });

    it("fails with CalldataOverflow when declared dynamic content is truncated", async () => {
      const { roles, member, testContractAddress, selector, allowFunction } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Bitmask,
              compValue: encodeCompValue(31, "ff", "00"),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      const malformedCall = concat([
        selector,
        encodeAbiParameters(parseAbiParameters("uint256, uint256"), [32n, 32n]),
        `0x${"11".repeat(31)}` as Hex,
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, malformedCall, 0],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.CalldataOverflow, 1n, anyValue],
      );
    });
  });

  describe("logic (single word)", () => {
    it("passes when (data & mask) == expected", async () => {
      const { allowFunction, invoke } = await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Bitmask,
              compValue: encodeCompValue(0, "ffff", "aabb"),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await invoke("0xaabb");
    });

    it("fails when (data & mask) != expected", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Bitmask,
              compValue: encodeCompValue(0, "ffff", "aabb"),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xaacc"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.BitmaskNotAllowed, 1n, anyValue],
      );
    });

    it("ignores bits outside the mask and rinses trailing garbage", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // mask 0xf0 checks only high nibble, expected 0xa0
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Bitmask,
              compValue: encodeCompValue(0, "f0", "a0"),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // 0xab & 0xf0 = 0xa0 -> passes (low nibble 0xb ignored)
      await invoke("0xab7777");

      // 0xaf & 0xf0 = 0xa0 -> passes (low nibble 0xf ignored)
      await invoke("0xaf8888888888");

      // 0xbb & 0xf0 = 0xb0 != 0xa0 -> fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xbb"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.BitmaskNotAllowed, 1n, anyValue],
      );
    });
  });

  describe("logic (multi-word)", () => {
    it("iterates chunks and passes when all match", async () => {
      const { allowFunction, invoke } = await loadFixture(setupDynamicParam);

      // 64-byte mask spanning 2 words
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Bitmask,
              compValue: encodeCompValue(0, "ff".repeat(64), "ab".repeat(64)),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await invoke("0x" + "ab".repeat(64));
    });

    it("fails on mismatch in any chunk (first or subsequent)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // 64-byte mask spanning 2 words
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Bitmask,
              compValue: encodeCompValue(0, "ff".repeat(64), "ab".repeat(64)),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // First byte wrong (first chunk mismatch)
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xcd" + "ab".repeat(63)),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.BitmaskNotAllowed, 1n, anyValue],
      );

      // Last byte wrong (second chunk mismatch)
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x" + "ab".repeat(63) + "cd"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.BitmaskNotAllowed, 1n, anyValue],
      );
    });
  });

  describe("shift offset", () => {
    it("applies shift correctly before reading data", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // shift 5 bytes, then check 1 byte
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Bitmask,
              compValue: encodeCompValue(5, "ff", "cd"),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // byte[5] = 0xcd -> passes
      await invoke("0x0000000000cd4444444444");

      // byte[5] = 0xab -> fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x0000000000ab"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.BitmaskNotAllowed, 1n, anyValue],
      );
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Bitmask,
              compValue: encodeCompValue(0, "ffff", "aabb"),
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xccdd"),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.BitmaskNotAllowed,
          1n, // Bitmask node at BFS index 1
          anyValue,
        ],
      );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Bitmask,
              compValue: encodeCompValue(0, "ffff", "aabb"),
            },
          ],
        }),
      );

      // 50 bytes of data, padded to 64 bytes
      const fiftyBytes =
        "0xccdd000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(fiftyBytes),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.BitmaskNotAllowed,
          anyValue,
          36n, // calldataOffset: dynamic param at byte 36 (4 + 32)
        ],
      );
    });
  });
});
