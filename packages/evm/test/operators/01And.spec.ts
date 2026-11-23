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
  packConditions,
} from "../utils.js";

const abiCoder = AbiCoder.defaultAbiCoder();

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupOneParam, setupTwoParams, setupDynamicParam } =
  createSetup(connection);

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
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.LessThan,
                  compValue: abiCoder.encode(["uint256"], [20]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 15 satisfies both: >10 AND <20
      await expect(invoke(15)).to.not.be.revert(ethers);
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
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.LessThan,
                  compValue: abiCoder.encode(["uint256"], [20]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 5 fails first child (GreaterThan 10), never evaluates second
      await expect(invoke(5))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterLessThanAllowed,
          2, // GreaterThan node
          anyValue,
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
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.LessThan,
                  compValue: abiCoder.encode(["uint256"], [20]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 25 passes first child (>10) but fails second (<20)
      await expect(invoke(25))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterGreaterThanAllowed,
          3, // LessThan node
          anyValue,
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
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
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

      // 50 satisfies both conditions on same payload
      await expect(invoke(50)).to.not.be.revert(ethers);
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
                      compValue: abiCoder.encode(["bytes"], ["0xaabbccdd"]),
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
                      compValue: abiCoder.encode(["bytes"], ["0xaabbccdd"]),
                    },
                    {
                      paramType: Encoding.Dynamic,
                      operator: Operator.EqualTo,
                      compValue: abiCoder.encode(["bytes"], ["0x11223344"]),
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
      const embedded = abiCoder.encode(
        ["bytes", "bytes"],
        ["0xaabbccdd", "0x11223344"],
      );

      // Passes both children
      await expect(invoke(embedded)).to.not.be.revert(ethers);

      // Wrong first bytes - fails both children
      const wrongFirst = abiCoder.encode(
        ["bytes", "bytes"],
        ["0xffffffff", "0x11223344"],
      );
      await expect(invoke(wrongFirst))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          4, // EqualTo node in first Matches child
          anyValue,
        );

      // Wrong second bytes - fails child 2
      const wrongSecond = abiCoder.encode(
        ["bytes", "bytes"],
        ["0xaabbccdd", "0xffffffff"],
      );
      await expect(invoke(wrongSecond))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          6, // Second EqualTo in second Matches child
          anyValue,
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
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
                // Non-structural: ether value must equal 123 (EtherValue -> empty payload)
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

      // Correct param + correct ether value
      await expect(invoke(42, { value: 123 })).to.not.be.revert(ethers);

      // Wrong param value
      await expect(invoke(99, { value: 123 }))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          2, // EqualTo node for param
          anyValue,
        );

      // Wrong ether value
      await expect(invoke(42, { value: 999 }))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          3, // EtherValue/EqualTo node
          anyValue,
        );
    });
  });

  describe("consumption propagation", () => {
    it("accumulates consumptions from multiple children in AND operator", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const allowanceKey = hexlify(randomBytes(32));
      // Set up allowance of 100
      await roles.setAllowance(allowanceKey, 100, 0, 0, 0, 0);

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
      await expect(invoke(30, 20)).to.not.be.revert(ethers);

      // Verify balance: 100 - 50 = 50
      const { balance } = await roles.accruedAllowance(allowanceKey);
      expect(balance).to.equal(50);

      // Try to consume 30 + 30 = 60.
      // Available: 50.
      // Should fail.
      await expect(invoke(30, 30))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          6, // Second WithinAllowance node
          anyValue,
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
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.LessThan,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
              ],
            },
          ],
        }),
      );

      // Fails first child (GreaterThan)
      await expect(invoke(5))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterLessThanAllowed,
          2, // GreaterThan node at BFS index 2
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
              operator: Operator.And,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.GreaterThan,
                  compValue: abiCoder.encode(["uint256"], [10]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.LessThan,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
              ],
            },
          ],
        }),
      );

      await expect(invoke(5))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterLessThanAllowed,
          anyValue,
          4, // calldataOffset: parameter starts at byte 4
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
                operator: Operator.And,
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
              operator: Operator.And,
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
      it("reverts UnsuitableChildCount when And has zero children", async () => {
        const { roles } = await loadFixture(setupTestContract);

        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.None,
              operator: Operator.And,
              compValue: "0x",
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "UnsuitableChildCount");
      });
    });
  });
});
