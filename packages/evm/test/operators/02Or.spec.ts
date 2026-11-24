import assert from "node:assert/strict";
import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import { network } from "hardhat";
import { encodeAbiParameters, parseAbiParameters, type Hex } from "viem";

import { createSetup } from "../setup.js";
import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
  packConditions,
} from "../utils.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupOneParam = setupFn("function fn(uint256)");
const setupDynamicParam = setupFn("function fn(bytes)");

describe("Operator - Or", () => {
  after(async () => {
    await connection.close();
  });

  describe("boolean logic", () => {
    it("passes when first child passes", async () => {
      const { allowFunction, invoke } = await loadFixture(setupOneParam);

      // Or: EqualTo(10) OR EqualTo(20)
      await allowFunction(
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
                    [10n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
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

      // 10 matches first child - passes immediately
      await invoke(10);
    });

    it("passes when second child passes after first fails", async () => {
      const { allowFunction, invoke } = await loadFixture(setupOneParam);

      // Or: EqualTo(10) OR EqualTo(20)
      await allowFunction(
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
                    [10n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
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

      // 20 fails first child, passes second child
      await invoke(20);
    });

    it("fails with OrViolation when all children fail", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      // Or: EqualTo(10) OR EqualTo(20)
      await allowFunction(
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
                    [10n],
                  ),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
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

      // 99 fails all children
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(99),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.OrViolation,
          1n, // Or node
          anyValue,
        ],
      );
    });
  });

  describe("payload routing", () => {
    it("passes same payload to structural children when non-variant", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      // Both children check the same parameter (non-variant: same payload to all)
      // Or: LessThan(10) OR GreaterThan(100)
      await allowFunction(
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
                  operator: Operator.LessThan,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [10n],
                  ),
                },
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

      // 5 passes first child (<10)
      await invoke(5);

      // 150 passes second child (>100)
      await invoke(150);

      // 50 fails both (not <10 and not >100)
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(50),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.OrViolation,
          1n, // Or node
          anyValue,
        ],
      );
    });

    it("passes individual child payloads when variant", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Or has two variant children that interpret the bytes param differently:
      // - Child 1: AbiEncoded with one Dynamic (checks bytes == 0xaabbccdd)
      // - Child 2: AbiEncoded with two Dynamics (checks first == 0x11111111)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.Or,
              children: [
                // Child 1: interpret as (bytes)
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
                // Child 2: interpret as (bytes, bytes)
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
                        ["0x11111111"],
                      ),
                    },
                    {
                      paramType: Encoding.Dynamic,
                      operator: Operator.Pass,
                    },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Matches child 1: single bytes = 0xaabbccdd
      const matchChild1 = encodeAbiParameters(parseAbiParameters("bytes"), [
        "0xaabbccdd",
      ]);
      await invoke(matchChild1);

      // Matches child 2: two bytes where first = 0x11111111
      const matchChild2 = encodeAbiParameters(
        parseAbiParameters("bytes, bytes"),
        ["0x11111111", "0xffffffff"],
      );
      await invoke(matchChild2);

      // Matches neither
      const matchNeither = encodeAbiParameters(parseAbiParameters("bytes"), [
        "0xdeadbeef",
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(matchNeither),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.OrViolation,
          1n, // Or node
          anyValue,
        ],
      );
    });

    it("passes empty payload to non-structural children", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      // Or with: structural child (checks param) OR non-structural (checks ether value)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.Or,
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
                // Non-structural: ether value must equal 123
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

      // Correct param, any ether - passes via first child
      await invoke(42);

      // Wrong param, correct ether - passes via second child
      await invoke(99, { value: 123 });

      // Wrong param, wrong ether - fails both
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(99, { value: 999 }),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.OrViolation,
          1n, // Or node
          anyValue,
        ],
      );
    });
  });

  describe("consumption handling", () => {
    it("returns consumptions only from the passing branch", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      const allowanceKeyA =
        "0x000000000000000000000000000000000000000000000000000000000000000a" as const;
      const allowanceKeyB =
        "0x000000000000000000000000000000000000000000000000000000000000000b" as const;

      // Set up two allowances of 100 each
      await roles.write.setAllowance([allowanceKeyA, 100n, 0n, 0n, 0n, 0n]);
      await roles.write.setAllowance([allowanceKeyB, 100n, 0n, 0n, 0n, 0n]);

      // Or with two branches, each consuming from different allowance
      // Child 1: value < 50 AND consume from allowanceA
      // Child 2: value >= 50 AND consume from allowanceB
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.Or,
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
                      compValue: allowanceKeyA,
                    },
                  ],
                },
                {
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.GreaterThan,
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [49n],
                      ),
                    },
                    {
                      paramType: Encoding.Static,
                      operator: Operator.WithinAllowance,
                      compValue: allowanceKeyB,
                    },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Call with value 30 - takes first branch, consumes from allowanceA
      await invoke(30);

      // Verify only allowanceA was consumed
      const [balanceA] = await roles.read.accruedAllowance([allowanceKeyA]);
      const [balanceB] = await roles.read.accruedAllowance([allowanceKeyB]);
      assert.equal(balanceA, 70n); // 100 - 30
      assert.equal(balanceB, 100n); // unchanged

      // Call with value 60 - takes second branch, consumes from allowanceB
      await invoke(60);

      // Verify only allowanceB was consumed this time
      const [balanceA2] = await roles.read.accruedAllowance([allowanceKeyA]);
      const [balanceB2] = await roles.read.accruedAllowance([allowanceKeyB]);
      assert.equal(balanceA2, 70n); // unchanged
      assert.equal(balanceB2, 40n); // 100 - 60
    });

    it("rolls back consumptions if a branch fails after consumption", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      const allowanceKeyA =
        "0x000000000000000000000000000000000000000000000000000000000000000a" as const;
      const allowanceKeyB =
        "0x000000000000000000000000000000000000000000000000000000000000000b" as const;

      await roles.write.setAllowance([allowanceKeyA, 100n, 0n, 0n, 0n, 0n]);
      await roles.write.setAllowance([allowanceKeyB, 100n, 0n, 0n, 0n, 0n]);

      // OR structure:
      // Branch 1: Consume 10 from A AND Fail (value > 999) -> Should rollback A
      // Branch 2: Consume 10 from B AND Pass (value > 0) -> Should commit B
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.Or,
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.WithinAllowance,
                      compValue: allowanceKeyA,
                    },
                    {
                      paramType: Encoding.Static,
                      operator: Operator.GreaterThan,
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [999n],
                      ),
                    },
                  ],
                },
                {
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.WithinAllowance,
                      compValue: allowanceKeyB,
                    },
                    {
                      paramType: Encoding.Static,
                      operator: Operator.GreaterThan,
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

      // Call with value 10
      await invoke(10);

      // Allowance A should be untouched (rolled back)
      const [balanceA] = await roles.read.accruedAllowance([allowanceKeyA]);
      assert.equal(balanceA, 100n);

      // Allowance B should be consumed
      const [balanceB] = await roles.read.accruedAllowance([allowanceKeyB]);
      assert.equal(balanceB, 90n);
    });

    it("rolls back a failed branch's charge to an allowance charged before the Or", async () => {
      // The consumption list shares entries between copies: a failed branch
      // that updated the shared entry (or list) in place would leak here.
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      const allowanceKey =
        "0x000000000000000000000000000000000000000000000000000000000000000a" as const;
      await roles.write.setAllowance([allowanceKey, 100n, 0n, 0n, 0n, 0n]);

      const withinAllowance = {
        paramType: Encoding.Static,
        operator: Operator.WithinAllowance,
        compValue: allowanceKey,
      };
      // And: charge A, then Or(charge A again and fail, pass)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                withinAllowance,
                {
                  paramType: Encoding.None,
                  operator: Operator.Or,
                  children: [
                    {
                      paramType: Encoding.None,
                      operator: Operator.And,
                      children: [
                        withinAllowance,
                        {
                          paramType: Encoding.Static,
                          operator: Operator.GreaterThan,
                          compValue: encodeAbiParameters(
                            parseAbiParameters("uint256"),
                            [999n],
                          ),
                        },
                      ],
                    },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke(10);

      // charged once
      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 90n);
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
              operator: Operator.Or,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
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
                    [20n],
                  ),
                },
              ],
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(99),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.OrViolation,
          1n, // Or node at BFS index 1
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
              operator: Operator.Or,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
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
                    [20n],
                  ),
                },
              ],
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(99),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.OrViolation,
          anyValue,
          4n, // calldataOffset: parameter starts at byte 4
        ],
      );
    });
  });

  describe("integrity", () => {
    describe("encoding", () => {
      it("reverts UnsuitableParameterType for invalid encodings", async () => {
        const { roles, evaluator } = await loadFixture(setupTestContract);

        for (const encoding of [
          Encoding.Static,
          Encoding.Dynamic,
          Encoding.Tuple,
          Encoding.Array,
          Encoding.AbiEncoded,
          Encoding.EtherValue,
        ]) {
          await viem.assertions.revertWithCustomError(
            packConditions(roles, [
              {
                parent: 0,
                paramType: encoding,
                operator: Operator.Or,
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
            "UnsuitableParameterType",
          );
        }
      });
    });

    describe("compValue", () => {
      it("reverts UnsuitableCompValue when compValue is not empty", async () => {
        const { roles, evaluator } = await loadFixture(setupTestContract);

        await viem.assertions.revertWithCustomError(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.None,
              operator: Operator.Or,
              compValue: "0x".padEnd(66, "0") as Hex,
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
    });

    describe("children", () => {
      it("reverts UnsuitableChildCount when Or has zero children", async () => {
        const { roles, evaluator } = await loadFixture(setupTestContract);

        await viem.assertions.revertWithCustomError(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.None,
              operator: Operator.Or,
              compValue: "0x",
            },
          ]),
          evaluator,
          "UnsuitableChildCount",
        );
      });
    });
  });
});
