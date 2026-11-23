import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { AbiCoder, hexlify, Interface, randomBytes, ZeroHash } from "ethers";
import type { BigNumberish } from "ethers";

const defaultAbiCoder = AbiCoder.defaultAbiCoder();

import { network } from "hardhat";

import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
  packConditions,
} from "../utils.js";
import { createSetup } from "../setup.js";
import type { Roles } from "../../typechain-types/index.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupOneParam = setupFn("function fn(uint256)");

describe("Operator - CallWithinAllowance", async () => {
  after(async () => {
    await connection.close();
  });

  async function setAllowance(
    roles: Roles,
    key: string,
    balance: BigNumberish,
    maxRefill: BigNumberish = 0,
    refill: BigNumberish = 0,
    period: BigNumberish = 0,
    timestamp: BigNumberish = 0,
  ) {
    await roles.setAllowance(
      key,
      balance,
      maxRefill,
      refill,
      period,
      timestamp,
    );
  }

  describe("CallWithinAllowance - Check", () => {
    async function setup() {
      const { roles, member, testContractAddress, roleKey } =
        await setupTestContract();
      const iface = new Interface(["function doNothing()"]);
      const fn = iface.getFunction("doNothing")!;

      const allowanceKey = hexlify(randomBytes(32));

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.CallWithinAllowance,
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        }),
      );
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.None,
      );

      async function invoke() {
        return roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, []),
            0,
          );
      }

      return {
        roles,
        member,
        allowanceKey,
        invoke,
      };
    }

    it("success - from existing balance", async () => {
      const { roles, allowanceKey, invoke } = await loadFixture(setup);

      await setAllowance(roles, allowanceKey, 1);

      expect((await roles.allowances(allowanceKey)).balance).to.equal(1);

      await expect(invoke())
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(allowanceKey, 1, 0);

      expect((await roles.allowances(allowanceKey)).balance).to.equal(0);

      await expect(invoke())
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          0, // CallWithinAllowance node (root)
          anyValue,
        );
    });

    it("success - multiple checks from existing balance", async () => {
      const { roles, allowanceKey, invoke } = await loadFixture(setup);

      await setAllowance(roles, allowanceKey, 2);

      expect((await roles.allowances(allowanceKey)).balance).to.equal(2);

      await expect(invoke()).to.not.be.revert(ethers);

      expect((await roles.allowances(allowanceKey)).balance).to.equal(1);

      await expect(invoke()).to.not.be.revert(ethers);

      expect((await roles.allowances(allowanceKey)).balance).to.equal(0);

      await expect(invoke())
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          0, // CallWithinAllowance node (root)
          anyValue,
        );
    });

    it("success - from balance 0 but enough refill pending", async () => {
      const { roles, allowanceKey, invoke } = await loadFixture(setup);

      const timestamp = await time.latest();
      await setAllowance(roles, allowanceKey, 0, 0, 1, 1000, timestamp - 1010);

      await expect(invoke()).to.not.be.revert(ethers);
      await expect(invoke())
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          0, // CallWithinAllowance node (root)
          anyValue,
        );
    });

    it("fail - insufficient balance and not enough elapsed for next refill", async () => {
      const { roles, allowanceKey, invoke } = await loadFixture(setup);

      const timestamp = await time.latest();
      await setAllowance(roles, allowanceKey, 0, 0, 1, 1000, timestamp);

      await expect(invoke())
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          0, // CallWithinAllowance node (root)
          anyValue,
        );
    });
  });

  describe("CallWithinAllowance - Variants", () => {
    it("enforces different call allowances per variant", async () => {
      const { roles, invoke, allowFunction } = await loadFixture(setupOneParam);

      const allowanceKey1 =
        "0x1000000000000000000000000000000000000000000000000000000000000001";
      const allowanceKey2 =
        "0x2000000000000000000000000000000000000000000000000000000000000002";
      const value1 = 100;
      const value2 = 200;
      const valueOther = 9999;

      await setAllowance(roles, allowanceKey1, 0);
      await setAllowance(roles, allowanceKey2, 1);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Or,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: defaultAbiCoder.encode(["uint256"], [value1]),
                    },
                  ],
                },
                {
                  paramType: Encoding.None,
                  operator: Operator.CallWithinAllowance,
                  compValue: defaultAbiCoder.encode(
                    ["bytes32"],
                    [allowanceKey1],
                  ),
                },
              ],
            },
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: defaultAbiCoder.encode(["uint256"], [value2]),
                    },
                  ],
                },
                {
                  paramType: Encoding.None,
                  operator: Operator.CallWithinAllowance,
                  compValue: defaultAbiCoder.encode(
                    ["bytes32"],
                    [allowanceKey2],
                  ),
                },
              ],
            },
          ],
        }),
      );

      await expect(invoke(valueOther))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.OrViolation,
          0, // Or node
          anyValue,
        );

      await expect(invoke(value1))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.OrViolation,
          0, // Or node
          anyValue,
        );

      await expect(invoke(value2)).not.to.be.revert(ethers);
      await expect(invoke(value2))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.OrViolation,
          0, // Or node
          anyValue,
        );
    });
  });

  describe("CallWithinAllowance - Logical Combinations", () => {
    it("AND(CallWithinAllowance, SomeParamComparison)", async () => {
      const { roles, invoke, allowFunction } = await loadFixture(setupOneParam);

      const allowanceKey =
        "0x0000000000000000000000000000000000000000000000000000000000000001";
      const allowedValue = 42;

      await setAllowance(roles, allowanceKey, 3);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: defaultAbiCoder.encode(
                    ["uint256"],
                    [allowedValue],
                  ),
                },
              ],
            },
            {
              paramType: Encoding.None,
              operator: Operator.CallWithinAllowance,
              compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
            },
          ],
        }),
      );

      // Wrong param value - should fail
      await expect(invoke(999))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          3, // EqualTo node
          anyValue,
        );

      // Correct param - should succeed (3 times)
      await expect(invoke(allowedValue)).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(2);

      await expect(invoke(allowedValue)).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(1);

      await expect(invoke(allowedValue)).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(0);

      // Now should fail due to exhausted allowance
      await expect(invoke(allowedValue))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          2, // CallWithinAllowance node
          anyValue,
        );
    });

    it("AND(CallWithinAllowance, OR(ParamA, ParamB))", async () => {
      const { roles, invoke, allowFunction } = await loadFixture(setupOneParam);

      const allowanceKey =
        "0x0000000000000000000000000000000000000000000000000000000000000001";
      const allowedValueA = 100;
      const allowedValueB = 200;

      await setAllowance(roles, allowanceKey, 4);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
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
                      compValue: defaultAbiCoder.encode(
                        ["uint256"],
                        [allowedValueA],
                      ),
                    },
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: defaultAbiCoder.encode(
                        ["uint256"],
                        [allowedValueB],
                      ),
                    },
                  ],
                },
              ],
            },
            {
              paramType: Encoding.None,
              operator: Operator.CallWithinAllowance,
              compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
            },
          ],
        }),
      );

      // Wrong param value (not A or B) - should fail
      await expect(invoke(999))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.OrViolation,
          3, // Or node
          anyValue,
        );

      // Allowed value A - should succeed
      await expect(invoke(allowedValueA)).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(3);

      // Allowed value B - should succeed
      await expect(invoke(allowedValueB)).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(2);

      // Allowed value A again - should succeed
      await expect(invoke(allowedValueA)).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(1);

      // Allowed value B again - should succeed
      await expect(invoke(allowedValueB)).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(0);

      // Both values should now fail due to exhausted allowance
      await expect(invoke(allowedValueA))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          2, // CallWithinAllowance node
          anyValue,
        );
      await expect(invoke(allowedValueB))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          2, // CallWithinAllowance node
          anyValue,
        );
    });

    it("CallWithinAllowance inside And as tuple field - Tuple(Static, And(CallWithinAllowance, Static))", async () => {
      const { member, roles, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface([
        "function twoParams(uint256 first, uint256 second)",
      ]);
      const fn = iface.getFunction("twoParams")!;

      const allowanceKey =
        "0x0000000000000000000000000000000000000000000000000000000000000001";

      await setAllowance(roles, allowanceKey, 2);

      // Structure: AbiEncoded -> Matches(Pass, And(EqualTo, CallWithinAllowance))
      // The And wraps CallWithinAllowance together with the field's structural check.
      // Type tree sees this as tuple(static, static).
      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Pass,
            },
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: defaultAbiCoder.encode(["uint256"], [42]),
                },
                {
                  paramType: Encoding.None,
                  operator: Operator.CallWithinAllowance,
                  compValue: defaultAbiCoder.encode(
                    ["bytes32"],
                    [allowanceKey],
                  ),
                },
              ],
            },
          ],
        }),
      );
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.None,
      );

      const invoke = (first: number, second: number) =>
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [first, second]),
            0,
          );

      // Wrong second param - should fail
      await expect(invoke(100, 999))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          3, // EqualTo: Matches[0] -> Pass[1], And[2] -> EqualTo[3], CallWithinAllowance[4]
          anyValue,
        );

      // Correct second param (42) - should succeed and consume allowance
      await expect(invoke(100, 42)).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(1);

      await expect(invoke(200, 42)).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(0);

      // Allowance exhausted - should fail
      await expect(invoke(300, 42))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          4, // CallWithinAllowance node
          anyValue,
        );
    });
  });

  describe("CallWithinAllowance - Standalone Root", () => {
    it("works as standalone root condition with allowTarget", async () => {
      const { member, roles, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface([
        "function doNothing()",
        "function doEvenLess()",
      ]);

      const allowanceKey =
        "0x0000000000000000000000000000000000000000000000000000000000000002";

      // Allowance of 2 calls
      await setAllowance(roles, allowanceKey, 2);

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.CallWithinAllowance,
          compValue: allowanceKey,
        }),
      );
      await roles.allowTargetPacked(
        roleKey,
        testContractAddress,
        packed,
        ExecutionOptions.Both,
      );

      const doNothingData = iface.encodeFunctionData("doNothing", []);
      const doEvenLessData = iface.encodeFunctionData("doEvenLess", []);

      // First call passes (allowance: 2 -> 1)
      await expect(
        roles
          .connect(member)
          .execTransactionWithRole(
            testContractAddress,
            0,
            doNothingData,
            0,
            roleKey,
          ),
      ).to.not.be.revert(ethers);

      // Second call passes (allowance: 1 -> 0)
      await expect(
        roles
          .connect(member)
          .execTransactionWithRole(
            testContractAddress,
            0,
            doEvenLessData,
            0,
            roleKey,
          ),
      ).to.not.be.revert(ethers);

      // Third call fails (allowance exhausted)
      await expect(
        roles
          .connect(member)
          .execTransactionWithRole(
            testContractAddress,
            0,
            doNothingData,
            0,
            roleKey,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          0, // CallWithinAllowance as root node
          anyValue,
        );
    });

    it("works as standalone root condition with allowFunction", async () => {
      const { member, roles, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface(["function doNothing()"]);
      const fn = iface.getFunction("doNothing")!;

      const allowanceKey =
        "0x0000000000000000000000000000000000000000000000000000000000000003";

      // Allowance of 3 calls to this specific function
      await setAllowance(roles, allowanceKey, 3);

      // CallWithinAllowance as the sole/root condition for a specific function
      const packedCondition = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.CallWithinAllowance,
          compValue: allowanceKey,
        }),
      );
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packedCondition,
        ExecutionOptions.None,
      );

      async function invoke() {
        return roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, []),
            0,
          );
      }

      expect((await roles.allowances(allowanceKey)).balance).to.equal(3);

      // First call passes (allowance: 3 -> 2)
      await expect(invoke()).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(2);

      // Second call passes (allowance: 2 -> 1)
      await expect(invoke()).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(1);

      // Third call passes (allowance: 1 -> 0)
      await expect(invoke()).to.not.be.revert(ethers);
      expect((await roles.allowances(allowanceKey)).balance).to.equal(0);

      // Fourth call fails (allowance exhausted)
      await expect(invoke())
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          0, // CallWithinAllowance as root node
          anyValue,
        );
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface(["function doNothing()"]);
      const fn = iface.getFunction("doNothing")!;
      const allowanceKey = hexlify(randomBytes(32));

      await setAllowance(roles, allowanceKey, 0); // No balance

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.CallWithinAllowance,
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        }),
      );
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.None,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, []),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          0, // CallWithinAllowance node (root)
          anyValue,
        );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface(["function doNothing()"]);
      const fn = iface.getFunction("doNothing")!;
      const allowanceKey = hexlify(randomBytes(32));

      await setAllowance(roles, allowanceKey, 0); // No balance

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.CallWithinAllowance,
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        }),
      );
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.None,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, []),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          anyValue,
          0, // calldataOffset: CallWithinAllowance has no payload
        );
    });
  });

  describe("integrity", () => {
    describe("encoding", () => {
      it("reverts UnsuitableParameterType for invalid encodings", async () => {
        const { roles, evaluator } = await loadFixture(setupTestContract);

        const allowanceKey = hexlify(randomBytes(32));

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
                operator: Operator.CallWithinAllowance,
                compValue: allowanceKey,
              },
            ]),
          ).to.be.revertedWithCustomError(evaluator, "UnsuitableParameterType");
        }
      });
    });

    describe("compValue", () => {
      it("reverts UnsuitableCompValue when compValue is not 32 bytes", async () => {
        const { roles, evaluator } = await loadFixture(setupTestContract);

        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.None,
              operator: Operator.CallWithinAllowance,
              compValue: "0x" + "ab".repeat(31), // 31 bytes
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
      });

      it("reverts UnsuitableCompValue when compValue is 33 bytes", async () => {
        const { roles, evaluator } = await loadFixture(setupTestContract);

        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.None,
              operator: Operator.CallWithinAllowance,
              compValue: "0x" + "ab".repeat(33), // 33 bytes
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
      });
    });

    describe("children", () => {
      it("reverts LeafNodeCannotHaveChildren when CallWithinAllowance has children", async () => {
        const { roles, evaluator } = await loadFixture(setupTestContract);

        const allowanceKey = hexlify(randomBytes(32));

        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.None,
              operator: Operator.CallWithinAllowance,
              compValue: allowanceKey,
            },
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            },
          ]),
        ).to.be.revertedWithCustomError(
          evaluator,
          "LeafNodeCannotHaveChildren",
        );
      });
    });
  });
});
