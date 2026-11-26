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
const setupOneParam = setupFn("function fn(uint256)");
const setupTwoParams = setupFn("function fn(uint256, uint256)");
const setupDynamicParam = setupFn("function fn(bytes)");

describe("Operator - And", () => {
  after(async () => {
    await connection.close();
  });

  describe("boolean logic", () => {
    it("passes when all children pass", async () => {
      const { allowFunction, invoke } = await loadFixture(setupOneParam);

      // And: GreaterThan(10) AND LessThan(20)
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
                  operator: Operator.GreaterThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [10n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.LessThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [20n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 15 satisfies both: >10 AND <20
      await invoke(15);
    });

    it("fails on first child and short-circuits", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      // And: GreaterThan(10) AND LessThan(20)
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
                  operator: Operator.GreaterThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [10n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.LessThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [20n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 5 fails first child (GreaterThan 10), never evaluates second
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(5),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterLessThanAllowed,
          2n, // GreaterThan node
          anyValue,
        ],
      );
    });

    it("fails on second child after first passes", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      // And: GreaterThan(10) AND LessThan(20)
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
                  operator: Operator.GreaterThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [10n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.LessThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [20n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 25 passes first child (>10) but fails second (<20)
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(25),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterGreaterThanAllowed,
          3n, // LessThan node
          anyValue,
        ],
      );
    });
  });

  describe("payload routing", () => {
    it("passes same payload to structural children when non-variant", async () => {
      const { allowFunction, invoke } = await loadFixture(setupOneParam);

      // Both children check the same parameter (non-variant: same payload to all)
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
                  operator: Operator.GreaterThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [10n],
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

      // 50 satisfies both conditions on same payload
      await invoke(50);
    });

    it("passes individual child payloads when variant", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // And has two variant children that interpret the bytes param differently:
      // - Child 1: AbiEncoded with one Dynamic (checks first bytes)
      // - Child 2: AbiEncoded with two Dynamics (checks both bytes)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                // Child 1: interpret as (bytes) - one dynamic
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000",
                  children: [
                    {
                      paramType: Encoding.Dynamic,
                      operator: Operator.EqualTo,
                      compValue: encodeAbiParameters(
                        parseAbiParameters("bytes"),
                        ["0xaabbccdd"],
                      ),
                    },
                  ],
                },
                // Child 2: interpret as (bytes, bytes) - two dynamics
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000",
                  children: [
                    {
                      paramType: Encoding.Dynamic,
                      operator: Operator.EqualTo,
                      compValue: encodeAbiParameters(
                        parseAbiParameters("bytes"),
                        ["0xaabbccdd"],
                      ),
                    },
                    {
                      paramType: Encoding.Dynamic,
                      operator: Operator.EqualTo,
                      compValue: encodeAbiParameters(
                        parseAbiParameters("bytes"),
                        ["0x11223344"],
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

      // Embedded bytes contains abi.encode(bytes, bytes)
      const embedded = encodeAbiParameters(parseAbiParameters("bytes, bytes"), [
        "0xaabbccdd",
        "0x11223344",
      ]);

      // Passes both children
      await invoke(embedded);

      // Wrong first bytes - fails both children
      const wrongFirst = encodeAbiParameters(
        parseAbiParameters("bytes, bytes"),
        ["0xffffffff", "0x11223344"],
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(wrongFirst),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          4n, // EqualTo node in first Matches child
          anyValue,
        ],
      );

      // Wrong second bytes - fails child 2
      const wrongSecond = encodeAbiParameters(
        parseAbiParameters("bytes, bytes"),
        ["0xaabbccdd", "0xffffffff"],
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(wrongSecond),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          6n, // Second EqualTo in second Matches child
          anyValue,
        ],
      );
    });

    it("passes empty payload to non-structural children", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      // And with: structural child (checks param) + non-structural (checks ether value)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                // Structural: param must equal 42
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [42n],
                  ),
                },
                // Non-structural: ether value must equal 123 (EtherValue -> empty payload)
                {
                  paramType: Encoding.EtherValue,
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

      // Correct param + correct ether value
      await invoke(42, { value: 123 });

      // Wrong param value
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(99, { value: 123 }),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          2n, // EqualTo node for param
          anyValue,
        ],
      );

      // Wrong ether value
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(42, { value: 999 }),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          3n, // EtherValue/EqualTo node
          anyValue,
        ],
      );
    });
  });

  describe("consumption propagation", () => {
    it("accumulates consumptions from multiple children in AND operator", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const allowanceKey = toHex(randomBytes(32));
      // Set up allowance of 100
      await roles.write.setAllowance([allowanceKey, 100n, 0n, 0n, 0n, 0n]);

      // Top-level AND combining two structural checks on the same payload
      // Child 1: Matches(arg0) -> WithinAllowance
      // Child 2: Matches(arg1) -> WithinAllowance
      await allowFunction(
        flattenCondition({
          paramType: Encoding.None, // Top-level AND must be None
          operator: Operator.And,
          children: [
            {
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
                  operator: Operator.Pass,
                },
              ],
            },
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Pass,
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

      // Execute transaction with [30, 20].
      // Child 1 (Matches) consumes 30.
      // Child 2 (Matches) consumes 20.
      // Total consumption: 50.
      await invoke(30, 20);

      // Verify balance: 100 - 50 = 50
      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 50n);

      // Try to consume 30 + 30 = 60.
      // Available: 50.
      // Should fail.
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(30, 30),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          6n, // Second WithinAllowance node
          anyValue,
        ],
      );
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

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
                  operator: Operator.GreaterThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [10n],
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
      );

      // Fails first child (GreaterThan)
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(5),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterLessThanAllowed,
          2n, // GreaterThan node at BFS index 2
          anyValue,
        ],
      );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

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
                  operator: Operator.GreaterThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [10n],
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
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(5),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterLessThanAllowed,
          anyValue,
          4n, // calldataOffset: parameter starts at byte 4
        ],
      );
    });
  });
});
