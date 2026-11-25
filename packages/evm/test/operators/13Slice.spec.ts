import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import { network } from "hardhat";
import {
  encodeAbiParameters,
  encodeFunctionData,
  encodePacked,
  parseAbiParameters,
  toHex,
  type Hex,
} from "viem";

import { toFlatNodes } from "../../../sdk/src/main/condition/checkStored.js";
import { packConditions } from "../../../sdk/src/main/condition/packConditions.js";
import { createSetup } from "../setup.js";
import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
} from "../utils.js";

// compValue layout: 2 bytes shift + 1 byte size
const encodeCompValue = (shift: number, size: number) =>
  encodePacked(["uint16", "uint8"], [shift, size]);

function replaceBytes(data: Hex, byteOffset: number, replacement: Hex): Hex {
  const hex = data.slice(2);
  const replacementHex = replacement.slice(2);
  const start = byteOffset * 2;
  const end = start + replacementHex.length;
  return `0x${hex.slice(0, start)}${replacementHex}${hex.slice(end)}` as Hex;
}

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupFn } = createSetup(connection);
const setupOneParam = setupFn("function fn(uint256)");
const setupDynamicParam = setupFn("function fn(bytes)");

describe("Operator - Slice", () => {
  after(async () => {
    await connection.close();
  });

  describe("extraction", () => {
    it("extracts 2-byte shift from compValue", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice 4 bytes at shift 4 (skip first 4 bytes)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(4, 4), // shift=4, size=4
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0xdeadbeefn],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // bytes: [4 bytes prefix][0xdeadbeef][suffix]
      // Slice extracts bytes 4-7 which should equal 0xdeadbeef
      await invoke("0x00000000deadbeef00000000");

      // Wrong value at the slice position
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x00000000cafebabe00000000"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 2n, anyValue],
      );

      // Value at wrong position (shift 0 instead of 4) - fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xdeadbeef0000000000000000"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 2n, anyValue],
      );
    });

    it("extracts 1-byte size from compValue (size 1)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice 1 byte at shift 0
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 1), // shift=0, size=1
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  // Single byte 0xab right-aligned to 32 bytes
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0xabn],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // bytes starting with 0xab - passes
      await invoke("0xab00000000000000");

      // bytes starting with 0xcd - fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xcd00000000000000"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 2n, anyValue],
      );
    });

    it("extracts 1-byte size from compValue (size 32)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice 32 bytes at shift 0 (full word)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 32), // shift=0, size=32
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [12345n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 32 bytes encoding 12345 - passes
      await invoke(
        encodeAbiParameters(parseAbiParameters("uint256"), [12345n]),
      );

      // 32 bytes encoding different value - fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(encodeAbiParameters(parseAbiParameters("uint256"), [12346n])),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 2n, anyValue],
      );
    });

    it("rejects dynamic slices beyond the declared byte length", async () => {
      const { roles, member, testContractAddress, fn, allowFunction } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(1, 4),
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0xdeadbeefn],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      const call = replaceBytes(
        encodeFunctionData({
          abi: [fn],
          functionName: fn.name,
          args: ["0x01"],
        }),
        69,
        "0xdeadbeef",
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, call, 0],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.CalldataOverflow, 1n, anyValue],
      );
    });
  });

  describe("propagation", () => {
    it("propagates result from child", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice 4 bytes, child checks GreaterThan 100
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4), // shift=0, size=4
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.GreaterThan,
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

      // Value 101 > 100 - child passes, Slice propagates success
      await invoke("0x00000065"); // 101 in 4 bytes

      // Value 100 not > 100 - child fails with ParameterLessThanAllowed, Slice propagates
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x00000064"), // 100 in 4 bytes
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterLessThanAllowed, 2n, anyValue],
      );
    });

    it("propagates consumption from child", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      const allowanceKey = toHex(randomBytes(32));

      // Set up allowance of 100
      await roles.write.setAllowance([allowanceKey, 100n, 0n, 0n, 0n, 0n]);

      // Slice 32 bytes, child consumes via WithinAllowance
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 32), // shift=0, size=32
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

      // Consume 30 from sliced value
      await invoke(encodeAbiParameters(parseAbiParameters("uint256"), [30n]));

      // Consumption propagated through Slice - remaining is 70
      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 70n);
    });

    it("frames a Bitmask child by the slice window", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice the first 4 bytes, then Bitmask them. The Bitmask operand must be
      // framed by the 4-byte window, not a full 32-byte word.
      // compValue: shift(0x0000) + mask(0xffffffff) + expected(0xdeadbeef)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4), // shift=0, size=4
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Bitmask,
                  compValue: "0x0000ffffffffdeadbeef",
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke("0xdeadbeefcafe");
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xcafebabe1234"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.BitmaskNotAllowed, anyValue, anyValue],
      );
    });

    it("reverts BitmaskOverflow when a Bitmask child's mask exceeds the slice window", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice window is 4 bytes; the Bitmask mask starts at shift 1 and spans 4
      // bytes (1 + 4 = 5 > 4), so it must overflow rather than read the 5th byte
      // that lies outside the sliced window.
      // compValue: shift(0x0001) + mask(0xffffffff) + expected(0x00000000)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4), // shift=0, size=4
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Bitmask,
                  compValue: "0x0001ffffffff00000000",
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xdeadbeefcafe"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.BitmaskOverflow, anyValue, anyValue],
      );
    });

    it("frames Bitmask under a Slice of a static operand", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Slice,
              compValue: encodeCompValue(28, 4),
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Bitmask,
                  compValue: "0x0000ffffffffdeadbeef",
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke(0xdeadbeef);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(0xcafebabe),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.BitmaskNotAllowed, anyValue, anyValue],
      );
    });

    it("propagates the narrowed frame through nested slices", async () => {
      const { roles, roleKey, testContractAddress, selector, invoke } =
        await loadFixture(setupDynamicParam);

      // Integrity rejects a Slice of a Slice: packed without it, to cover how it
      // is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(1, 6),
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Slice,
                  compValue: encodeCompValue(0, 4),
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.Bitmask,
                      compValue: "0x0000ffffffffdeadbeef",
                    },
                  ],
                },
              ],
            },
          ],
        }),
      );
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        toHex(packConditions(flat)),
        ExecutionOptions.Both,
      ]);

      await invoke("0xaadeadbeefbbcc");
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xaacafebabebbcc"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.BitmaskNotAllowed, anyValue, anyValue],
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
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4), // shift=0, size=4
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0xdeadbeefn],
                  ),
                },
              ],
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xcafebabe"),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          2n, // EqualTo node at BFS index 2
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
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4), // shift=0, size=4
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0xdeadbeefn],
                  ),
                },
              ],
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xcafebabe"),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          anyValue,
          68n, // calldataOffset: bytes data at byte 68 (4 + 32 + 32)
        ],
      );
    });
  });
});
