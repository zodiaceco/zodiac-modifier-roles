import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import { network } from "hardhat";
import {
  concat,
  encodeAbiParameters,
  encodeFunctionData,
  parseAbi,
  parseAbiParameters,
  toFunctionSelector,
  toHex,
  type Hex,
} from "viem";

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
const setupOneParam = setupFn("function fn(uint256)");
const setupTwoParams = setupFn("function fn(uint256, uint256)");
const setupDynamicParam = setupFn("function fn(bytes)");
const setupTupleWithBytes = setupFn("function fn((bytes, uint256))");

describe("Operator - Matches", () => {
  after(async () => {
    await connection.close();
  });

  describe("prefix skipping", () => {
    it("skips 10 bytes offset before decoding child", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Matches with AbiEncoded that skips 10 bytes (0x000a) but does NOT match them
      // compValue length is 2 => only configuration, no match bytes
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x000a", // 10 bytes offset
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

      // Send payload with 10 bytes of random junk + encoded param
      // The junk should be skipped, not matched.
      const junkHeader = toHex(randomBytes(10));
      const correctPayload = concat([
        junkHeader,
        encodeAbiParameters(parseAbiParameters("uint256"), [42n]),
      ]);

      await invoke(correctPayload);

      // Ensure that actual logic checks the param (42)
      const wrongParamPayload = concat([
        junkHeader,
        encodeAbiParameters(parseAbiParameters("uint256"), [99n]),
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(wrongParamPayload),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          2n, // EqualTo node
          anyValue,
        ],
      );
    });
  });
  describe("prefix validation", () => {
    it("validates 4-byte prefix (shift 4)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Matches with 4-byte prefix (common selector size)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef", // 2 bytes length + 4 bytes prefix
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

      // Correct 4-byte prefix + valid param passes
      const correctPayload = concat([
        "0xdeadbeef",
        encodeAbiParameters(parseAbiParameters("uint256"), [42n]),
      ]);
      await invoke(correctPayload);

      // Wrong 4-byte prefix fails
      const wrongPayload = concat([
        "0xcafebabe",
        encodeAbiParameters(parseAbiParameters("uint256"), [42n]),
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(wrongPayload),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.LeadingBytesNotAMatch,
          1n, // Matches node with prefix
          anyValue,
        ],
      );
    });

    it("validates 4-byte prefix at the former 2^60 false-rejection boundary", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Regression: the prefix comparison must only cover the N prefix
      // bytes. With the old 28-bit shift, 2^60 leaked into the comparison
      // window and caused a false LeadingBytesNotAMatch rejection.
      const bigValue = 2n ** 60n;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef", // 2 bytes length + 4 bytes prefix
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [bigValue],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Correct prefix + large param value passes
      const payload = concat([
        "0xdeadbeef",
        encodeAbiParameters(parseAbiParameters("uint256"), [bigValue]),
      ]);
      await invoke(payload);

      // Wrong prefix still fails with LeadingBytesNotAMatch
      const wrongPayload = concat([
        "0xcafebabe",
        encodeAbiParameters(parseAbiParameters("uint256"), [bigValue]),
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(wrongPayload),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.LeadingBytesNotAMatch,
          1n, // Matches node with prefix
          anyValue,
        ],
      );
    });

    it("skips prefix check when compValue is empty (shift 0)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Matches with empty compValue - no prefix check
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0000", // 2 bytes length (0) = no prefix to check
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
        ExecutionOptions.None,
      );

      // Wrong param value fails with ParameterNotAllowed, not LeadingBytesNotAMatch
      const payload = encodeAbiParameters(parseAbiParameters("uint256"), [
        999n,
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(payload),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          2n, // EqualTo node
          anyValue,
        ],
      );
    });

    it("validates 10-byte prefix (shift 10)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      const prefix10 = toHex(randomBytes(10));

      // Matches with 10-byte prefix
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: concat(["0x000a", prefix10]), // 2 bytes length + 10 bytes prefix
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [123n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Correct 10-byte prefix + valid param passes
      const correctPayload = concat([
        prefix10,
        encodeAbiParameters(parseAbiParameters("uint256"), [123n]),
      ]);
      await invoke(correctPayload);

      // Wrong 10-byte prefix fails with LeadingBytesNotAMatch
      const wrongPrefix10 = toHex(randomBytes(10));
      const wrongPrefixPayload = concat([
        wrongPrefix10,
        encodeAbiParameters(parseAbiParameters("uint256"), [123n]),
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(wrongPrefixPayload),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.LeadingBytesNotAMatch,
          1n, // Matches node with prefix
          anyValue,
        ],
      );

      // Correct prefix + wrong param fails with ParameterNotAllowed
      const wrongParamPayload = concat([
        prefix10,
        encodeAbiParameters(parseAbiParameters("uint256"), [999n]),
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(wrongParamPayload),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          2n, // EqualTo node
          anyValue,
        ],
      );
    });

    it("validates 31-byte prefix (shift 31)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      const prefix31 = toHex(randomBytes(31));

      // Matches with 31-byte prefix
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: concat(["0x001f", prefix31]), // 2 bytes length + 31 bytes prefix
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [456n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // Correct 31-byte prefix + valid param passes
      const correctPayload = concat([
        prefix31,
        encodeAbiParameters(parseAbiParameters("uint256"), [456n]),
      ]);
      await invoke(correctPayload);

      // Wrong 31-byte prefix fails
      const wrongPrefix31 = toHex(randomBytes(31));
      const wrongPayload = concat([
        wrongPrefix31,
        encodeAbiParameters(parseAbiParameters("uint256"), [456n]),
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(wrongPayload),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.LeadingBytesNotAMatch,
          1n, // Matches node with prefix
          anyValue,
        ],
      );
    });
  });

  describe("parameter routing", () => {
    it("routes decoded parameters to corresponding children", async () => {
      const abi = parseAbi(["function fn(uint256,uint256,uint256)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      // Matches routes each param to its corresponding child
      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                100n,
              ]),
            },
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                200n,
              ]),
            },
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                300n,
              ]),
            },
          ],
        }),
        ExecutionOptions.Both,
      ]);

      // All params match - passes
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [100n, 200n, 300n],
          }),
          0,
        ],
        { account: member.account },
      );

      // First param wrong - fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [999n, 200n, 300n],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          1n, // First EqualTo node
          anyValue,
        ],
      );

      // Second param wrong - fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [100n, 999n, 300n],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          2n, // Second EqualTo node
          anyValue,
        ],
      );

      // Third param wrong - fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [100n, 200n, 999n],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          3n, // Third EqualTo node
          anyValue,
        ],
      );
    });

    it("passes empty payload to non-structural children", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            // Structural: Matches checks param
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
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
            // Non-structural: checks ether value (sibling of Matches)
            {
              paramType: Encoding.EtherValue,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                100n,
              ]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Correct param + correct ether
      await invoke(42, { value: 100 });

      // Correct param + wrong ether
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(42, { value: 999 }),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          2n, // EtherValue EqualTo node (BFS: And=0, Matches=1, EtherValue=2, Static=3)
          anyValue,
        ],
      );
    });

    it("accumulates consumptions across children", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const allowanceKey =
        "0x000000000000000000000000000000000000000000000000000000000000abcd" as const;

      // Set up allowance of 100
      await roles.write.setAllowance([allowanceKey, 100n, 0n, 0n, 0n, 0n]);

      // Matches with two children consuming from same allowance
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
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
        }),
        ExecutionOptions.Both,
      );

      // First call: 30 + 20 = 50 consumed
      await invoke(30, 20);

      // Verify consumption was accumulated
      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 50n);

      // Second call: 30 + 30 = 60, but only 50 remaining
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(30, 30),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          2n, // Second WithinAllowance node
          anyValue,
        ],
      );
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Pass,
            },
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                42n,
              ]),
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(100, 99),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          2n, // EqualTo child node at BFS index 2
          anyValue,
        ],
      );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Pass,
            },
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                42n,
              ]),
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(100, 99),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          anyValue,
          36n, // calldataOffset: second param starts at byte 36 (4 + 32)
        ],
      );
    });
  });

  describe("Tuple traversal", () => {
    it("passes when all tuple children match", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const abi = parseAbi(["function fn((uint256,uint256))"]);
      const selector = toFunctionSelector(abi[0]);

      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
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
      ]);

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [[100n, 200n]],
          }),
          0,
        ],
        { account: member.account },
      );
    });

    it("reverts CalldataOverflow when tuple head is truncated", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const selector = "0xaabbccdd";

      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      ]);

      // Only 32 bytes but tuple needs 64
      const truncatedData = (selector + "00".repeat(32)) as Hex;

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, truncatedData, 0],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.CalldataOverflow, anyValue, anyValue],
      );
    });

    it("reverts CalldataOverflow when inline element exceeds bounds", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const selector = "0xaabbccdd";

      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      ]);

      // 48 bytes - first element OK, second element truncated
      const truncatedData = (selector + "00".repeat(48)) as Hex;

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, truncatedData, 0],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.CalldataOverflow, anyValue, anyValue],
      );
    });

    it("reverts ParameterNotAllowed when tuple child value mismatches", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const abi = parseAbi(["function fn((uint256,uint256))"]);
      const selector = toFunctionSelector(abi[0]);

      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
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
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [[100n, 999n]],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, anyValue, anyValue],
      );
    });
  });

  describe("Array traversal", () => {
    it("reverts CalldataOverflow when array length slot is truncated", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const selector = "0xaabbccdd";

      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.Matches,
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      ]);

      // Pointer to offset 32, but only 16 bytes at that location
      const truncatedData = (selector +
        "0000000000000000000000000000000000000000000000000000000000000020" +
        "00".repeat(16)) as Hex;

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, truncatedData, 0],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.CalldataOverflow, anyValue, anyValue],
      );
    });

    it("reverts CalldataOverflow when element exceeds bounds", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const selector = "0xaabbccdd";

      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      ]);

      // Array claims 3 elements but only 2 slots of data provided
      const truncatedData = (selector +
        "0000000000000000000000000000000000000000000000000000000000000020" +
        "0000000000000000000000000000000000000000000000000000000000000003" +
        "00".repeat(64)) as Hex;

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, truncatedData, 0],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.CalldataOverflow, anyValue, anyValue],
      );
    });

    it("reverts with ParameterNotAMatch when array shorter than expected", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const abi = parseAbi(["function fn(uint256[])"]);
      const selector = toFunctionSelector(abi[0]);

      // Condition expects exactly 2 elements
      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.Matches,
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
      ]);

      // Array with only 1 element - expects 2
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "fn", args: [[100n]] }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAMatch, anyValue, anyValue],
      );
    });

    it("reverts with ParameterNotAMatch when array longer than expected", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const abi = parseAbi(["function fn(uint256[])"]);
      const selector = toFunctionSelector(abi[0]);

      // Condition expects exactly 2 elements
      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.Matches,
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
      ]);

      // Array with 3 elements - first two match, but third element exceeds condition count
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [[100n, 200n, 300n]],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAMatch, anyValue, anyValue],
      );
    });

    it("reverts with ParameterNotAllowed when one item does not match", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const abi = parseAbi(["function fn(uint256[])"]);
      const selector = toFunctionSelector(abi[0]);

      // Condition expects exactly 2 elements with specific values
      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.Matches,
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
      ]);

      // Array with correct length but wrong value for second element
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [[100n, 999n]],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 3n, anyValue],
      );
    });
  });

  describe("AbiEncoded traversal", () => {
    it("passes when nested AbiEncoded matches", async () => {
      const { allowFunction, invoke } = await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef",
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

      const payload = concat([
        "0xdeadbeef",
        encodeAbiParameters(parseAbiParameters("uint256"), [42n]),
      ]);
      await invoke(payload);
    });

    it("reverts CalldataOverflow when nested payload is truncated", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef",
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 4-byte selector + only 16 bytes (need 32)
      const truncatedPayload = ("0xdeadbeef" + "00".repeat(16)) as Hex;
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(truncatedPayload),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.CalldataOverflow, anyValue, anyValue],
      );
    });

    it("reverts LeadingBytesNotAMatch when prefix does not match", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef",
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      const wrongPrefixPayload = concat([
        "0xcafebabe",
        encodeAbiParameters(parseAbiParameters("uint256"), [42n]),
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(wrongPrefixPayload),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.LeadingBytesNotAMatch, anyValue, anyValue],
      );
    });

    it("reverts ParameterNotAllowed when decoded child mismatches", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef",
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

      const wrongValuePayload = concat([
        "0xdeadbeef",
        encodeAbiParameters(parseAbiParameters("uint256"), [999n]),
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(wrongValuePayload),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, anyValue, anyValue],
      );
    });

    it("matches a nested call without parameters by its selector", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef",
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke("0xdeadbeef");

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xcafebabe"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.LeadingBytesNotAMatch, anyValue, anyValue],
      );
    });

    it("compares a tuple holding nested calldata, described without children", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(
        setupTupleWithBytes,
      );

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(
                parseAbiParameters("(bytes, uint256)"),
                [["0xdeadbeef", 5n]],
              ),
              children: [
                { paramType: Encoding.AbiEncoded, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke(["0xdeadbeef", 5n]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(["0xdeadbeef", 6n]),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, anyValue, anyValue],
      );
    });
  });

  describe("Or branches", () => {
    it("allows functions without parameters by selector, on a target", async () => {
      const { roles, member, testContractAddress, allowTarget } =
        await loadFixture(setupTestContract);

      const bySelector = (signature: string) => ({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        compValue: concat(["0x0004", toFunctionSelector(signature)]),
      });
      await allowTarget(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Or,
          children: [bySelector("pause()"), bySelector("unpause()")],
        }),
        ExecutionOptions.Both,
      );

      const exec = (signature: string) =>
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, toFunctionSelector(signature), 0],
          { account: member.account },
        );

      await exec("pause()");
      await exec("unpause()");

      await viem.assertions.revertWithCustomErrorWithArgs(
        exec("kill()"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.OrViolation, anyValue, anyValue],
      );
    });

    it("passes when one branch succeeds", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const abi = parseAbi(["function fn(uint256)"]);
      const selector = toFunctionSelector(abi[0]);

      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
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
      ]);

      // First branch matches
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({ abi, functionName: "fn", args: [100n] }),
          0,
        ],
        { account: member.account },
      );

      // Second branch matches
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({ abi, functionName: "fn", args: [200n] }),
          0,
        ],
        { account: member.account },
      );
    });

    it("passes when one branch overflows and other succeeds", async () => {
      const { allowFunction, invoke } = await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.Or,
              children: [
                // Branch 1: expects 2 static params (will overflow with 1)
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000",
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
                // Branch 2: expects 1 static param (will succeed)
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000",
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Single uint256 - first branch overflows, second succeeds
      const payload = encodeAbiParameters(parseAbiParameters("uint256"), [42n]);
      await invoke(payload);
    });

    it("reverts OrViolation when all branches fail validation", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const abi = parseAbi(["function fn(uint256)"]);
      const selector = toFunctionSelector(abi[0]);

      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
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
      ]);

      // Neither branch matches
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "fn", args: [999n] }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.OrViolation, anyValue, anyValue],
      );
    });

    it("reverts OrViolation when all branches overflow", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.Or,
              children: [
                // Branch 1: expects 1 static param
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000",
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [0n],
                      ),
                    },
                  ],
                },
                // Branch 2: expects 2 static params
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000",
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [0n],
                      ),
                    },
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [0n],
                      ),
                    },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Empty bytes - both branches will overflow
      const emptyPayload = "0x";
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(emptyPayload),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.OrViolation, anyValue, anyValue],
      );
    });
  });
});
