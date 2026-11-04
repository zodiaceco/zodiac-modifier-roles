import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { AbiCoder } from "ethers";

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

const abiCoder = AbiCoder.defaultAbiCoder();

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupOneParam, setupDynamicParam } =
  createSetup(connection);

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
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [20]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 10 matches first child - passes immediately
      await expect(invoke(10)).to.not.be.revert(ethers);
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
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [20]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 20 fails first child, passes second child
      await expect(invoke(20)).to.not.be.revert(ethers);
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
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [20]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 99 fails all children
      await expect(invoke(99))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.OrViolation,
          1, // Or node
          anyValue,
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
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.GreaterThan,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 5 passes first child (<10)
      await expect(invoke(5)).to.not.be.revert(ethers);

      // 150 passes second child (>100)
      await expect(invoke(150)).to.not.be.revert(ethers);

      // 50 fails both (not <10 and not >100)
      await expect(invoke(50))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.OrViolation,
          1, // Or node
          anyValue,
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
                      compValue: abiCoder.encode(["bytes"], ["0xaabbccdd"]),
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
                      compValue: abiCoder.encode(["bytes"], ["0x11111111"]),
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
      const matchChild1 = abiCoder.encode(["bytes"], ["0xaabbccdd"]);
      await expect(invoke(matchChild1)).to.not.be.revert(ethers);

      // Matches child 2: two bytes where first = 0x11111111
      const matchChild2 = abiCoder.encode(
        ["bytes", "bytes"],
        ["0x11111111", "0xffffffff"],
      );
      await expect(invoke(matchChild2)).to.not.be.revert(ethers);

      // Matches neither
      const matchNeither = abiCoder.encode(["bytes"], ["0xdeadbeef"]);
      await expect(invoke(matchNeither))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.OrViolation,
          1, // Or node
          anyValue,
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
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
                // Non-structural: ether value must equal 123
                {
                  paramType: Encoding.EtherValue,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [123]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Correct param, any ether - passes via first child
      await expect(invoke(42)).to.not.be.revert(ethers);

      // Wrong param, correct ether - passes via second child
      await expect(invoke(99, { value: 123 })).to.not.be.revert(ethers);

      // Wrong param, wrong ether - fails both
      await expect(invoke(99, { value: 999 }))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.OrViolation,
          1, // Or node
          anyValue,
        );
    });
  });

  describe("consumption handling", () => {
    it("returns consumptions only from the passing branch", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      const allowanceKeyA =
        "0x000000000000000000000000000000000000000000000000000000000000000a";
      const allowanceKeyB =
        "0x000000000000000000000000000000000000000000000000000000000000000b";

      // Set up two allowances of 100 each
      await roles.setAllowance(allowanceKeyA, 100, 0, 0, 0, 0);
      await roles.setAllowance(allowanceKeyB, 100, 0, 0, 0, 0);

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
                      compValue: abiCoder.encode(["uint256"], [50]),
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
                      compValue: abiCoder.encode(["uint256"], [49]),
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
      await expect(invoke(30)).to.not.be.revert(ethers);

      // Verify only allowanceA was consumed
      const { balance: balanceA } = await roles.accruedAllowance(allowanceKeyA);
      const { balance: balanceB } = await roles.accruedAllowance(allowanceKeyB);
      expect(balanceA).to.equal(70); // 100 - 30
      expect(balanceB).to.equal(100); // unchanged

      // Call with value 60 - takes second branch, consumes from allowanceB
      await expect(invoke(60)).to.not.be.revert(ethers);

      // Verify only allowanceB was consumed this time
      const { balance: balanceA2 } =
        await roles.accruedAllowance(allowanceKeyA);
      const { balance: balanceB2 } =
        await roles.accruedAllowance(allowanceKeyB);
      expect(balanceA2).to.equal(70); // unchanged
      expect(balanceB2).to.equal(40); // 100 - 60
    });

    it("rolls back consumptions if a branch fails after consumption", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      const allowanceKeyA =
        "0x000000000000000000000000000000000000000000000000000000000000000a";
      const allowanceKeyB =
        "0x000000000000000000000000000000000000000000000000000000000000000b";

      await roles.setAllowance(allowanceKeyA, 100, 0, 0, 0, 0);
      await roles.setAllowance(allowanceKeyB, 100, 0, 0, 0, 0);

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
                      compValue: abiCoder.encode(["uint256"], [999]),
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
                      compValue: abiCoder.encode(["uint256"], [0]),
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
      await expect(invoke(10)).to.not.be.revert(ethers);

      // Allowance A should be untouched (rolled back)
      const { balance: balanceA } = await roles.accruedAllowance(allowanceKeyA);
      expect(balanceA).to.equal(100);

      // Allowance B should be consumed
      const { balance: balanceB } = await roles.accruedAllowance(allowanceKeyB);
      expect(balanceB).to.equal(90);
    });

    it("rolls back a failed branch's charge to an allowance charged before the Or", async () => {
      // The consumption list shares entries between copies: a failed branch
      // that updated the shared entry (or list) in place would leak here.
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      const allowanceKey =
        "0x000000000000000000000000000000000000000000000000000000000000000a";
      await roles.setAllowance(allowanceKey, 100, 0, 0, 0, 0);

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
                          compValue: abiCoder.encode(["uint256"], [999]),
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

      await expect(invoke(10)).to.not.be.revert(ethers);

      // charged once
      const { balance } = await roles.accruedAllowance(allowanceKey);
      expect(balance).to.equal(90);
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
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [20]),
                },
              ],
            },
          ],
        }),
      );

      await expect(invoke(99))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.OrViolation,
          1, // Or node at BFS index 1
          anyValue,
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
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [20]),
                },
              ],
            },
          ],
        }),
      );

      await expect(invoke(99))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.OrViolation,
          anyValue,
          4, // payloadLocation: parameter starts at byte 4
        );
    });
  });

  describe("integrity", () => {
    describe("encoding", () => {
      it("reverts UnsuitableParameterType for invalid encodings", async () => {
        const { roles } = await loadFixture(setupTestContract);

        for (const encoding of [
          Encoding.Static,
          Encoding.Dynamic,
          Encoding.Tuple,
          Encoding.Array,
          Encoding.AbiEncoded,
          Encoding.EtherValue,
        ]) {
          await expect(
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
          ).to.be.revertedWithCustomError(roles, "UnsuitableParameterType");
        }
      });
    });

    describe("compValue", () => {
      it("reverts UnsuitableCompValue when compValue is not empty", async () => {
        const { roles } = await loadFixture(setupTestContract);

        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.None,
              operator: Operator.Or,
              compValue: "0x".padEnd(66, "0"),
            },
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");
      });
    });

    describe("children", () => {
      it("reverts UnsuitableChildCount when Or has zero children", async () => {
        const { roles } = await loadFixture(setupTestContract);

        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.None,
              operator: Operator.Or,
              compValue: "0x",
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "UnsuitableChildCount");
      });
    });
  });
});
