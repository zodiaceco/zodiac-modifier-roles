import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { AbiCoder, Interface, solidityPacked } from "ethers";

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

const defaultAbiCoder = AbiCoder.defaultAbiCoder();

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupDynamicParam = setupFn("function fn(bytes)");
const setupOneParamSigned = setupFn("function fn(int256)");

describe("Operator - SignedIntLessThan", () => {
  after(async () => {
    await connection.close();
  });

  it("passes when signed value < compValue", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupOneParamSigned);

    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.SignedIntLessThan,
            compValue: defaultAbiCoder.encode(["int256"], [100]),
          },
        ],
      }),
    );

    // 99 < 100 passes
    await expect(invoke(99)).to.not.be.revert(ethers);
  });

  it("fails when signed value >= compValue", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupOneParamSigned);

    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.SignedIntLessThan,
            compValue: defaultAbiCoder.encode(["int256"], [100]),
          },
        ],
      }),
    );

    // 100 == 100 fails
    await expect(invoke(100))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        1,
        anyValue,
      );

    // 101 > 100 fails
    await expect(invoke(101))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        1,
        anyValue,
      );
  });

  it("handles negative numbers correctly", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupOneParamSigned);

    // compValue = -50, so value must be < -50
    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.SignedIntLessThan,
            compValue: defaultAbiCoder.encode(["int256"], [-50]),
          },
        ],
      }),
    );

    // -51 < -50 passes
    await expect(invoke(-51)).to.not.be.revert(ethers);

    // -100 < -50 passes
    await expect(invoke(-100)).to.not.be.revert(ethers);

    // -50 == -50 fails
    await expect(invoke(-50))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        1,
        anyValue,
      );

    // -49 > -50 fails
    await expect(invoke(-49))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        1,
        anyValue,
      );

    // 0 > -50 fails
    await expect(invoke(0))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        1,
        anyValue,
      );
  });

  it("integrates with Slice operator", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupDynamicParam);

    // 1. Slice 4 bytes at offset 0, then SignedIntLessThan 100
    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Dynamic,
            operator: Operator.Slice,
            compValue: solidityPacked(["uint16", "uint8"], [0, 4]), // shift=0, size=4
            children: [
              {
                paramType: Encoding.Static,
                operator: Operator.SignedIntLessThan,
                compValue: defaultAbiCoder.encode(["int256"], [100]),
              },
            ],
          },
        ],
      }),
    );

    // 0x00000063 = 99 < 100 passes
    await expect(invoke("0x00000063")).to.not.be.revert(ethers);

    // 0x00000064 = 100 >= 100 fails
    await expect(invoke("0x00000064"))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        2,
        anyValue,
      );

    // 0xffffffff = -1 < 100 passes (the window is sign-extended)
    await expect(invoke("0xffffffff")).to.not.be.revert(ethers);

    // 0x80000000 = int32 min < 100 passes
    await expect(invoke("0x80000000")).to.not.be.revert(ethers);

    // 0x7fffffff = int32 max >= 100 fails
    await expect(invoke("0x7fffffff"))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        2,
        anyValue,
      );

    // 2. Slice 32 bytes (full int256) at offset 0, then SignedIntLessThan -100
    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Dynamic,
            operator: Operator.Slice,
            compValue: solidityPacked(["uint16", "uint8"], [0, 32]), // shift=0, size=32
            children: [
              {
                paramType: Encoding.Static,
                operator: Operator.SignedIntLessThan,
                compValue: defaultAbiCoder.encode(["int256"], [-100]),
              },
            ],
          },
        ],
      }),
    );

    // -150 (32 bytes) < -100 -> Pass
    const neg150 = solidityPacked(["int256"], [-150]);
    await expect(invoke(neg150)).to.not.be.revert(ethers);

    // -100 (32 bytes) < -100 -> Fail (Equal)
    const neg100 = solidityPacked(["int256"], [-100]);
    await expect(invoke(neg100))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        2,
        anyValue,
      );

    // -99 (32 bytes) < -100 -> Fail (Greater)
    const neg99 = solidityPacked(["int256"], [-99]);
    await expect(invoke(neg99))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        2,
        anyValue,
      );

    // 3. Slice 4 bytes (packed int32) at offset 0, then SignedIntLessThan -100
    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Dynamic,
            operator: Operator.Slice,
            compValue: solidityPacked(["uint16", "uint8"], [0, 4]), // shift=0, size=4
            children: [
              {
                paramType: Encoding.Static,
                operator: Operator.SignedIntLessThan,
                compValue: defaultAbiCoder.encode(["int256"], [-100]),
              },
            ],
          },
        ],
      }),
    );

    // -150 (4 bytes) < -100 -> Pass
    await expect(invoke(solidityPacked(["int32"], [-150]))).to.not.be.revert(
      ethers,
    );

    // -100 (4 bytes) < -100 -> Fail (Equal)
    await expect(invoke(solidityPacked(["int32"], [-100])))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        2,
        anyValue,
      );

    // -99 (4 bytes) < -100 -> Fail (Greater)
    await expect(invoke(solidityPacked(["int32"], [-99])))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        2,
        anyValue,
      );

    // 50 (4 bytes) < -100 -> Fail (Greater)
    await expect(invoke(solidityPacked(["int32"], [50])))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        2,
        anyValue,
      );
  });

  it("compares ether value (msg.value)", async () => {
    const { roles, member, testContractAddress, roleKey } =
      await loadFixture(setupTestContract);
    const iface = new Interface(["function fn()"]);
    const fn = iface.getFunction("fn")!;

    // SignedIntLessThan on EtherValue: msg.value must be < 1000 wei
    const packed = await packConditions(
      roles,
      flattenCondition({
        paramType: Encoding.EtherValue,
        operator: Operator.SignedIntLessThan,
        compValue: defaultAbiCoder.encode(["int256"], [1000]),
      }),
    );
    await roles.allowFunctionPacked(
      roleKey,
      testContractAddress,
      fn.selector,
      packed,
      ExecutionOptions.Send,
    );

    // 999 < 1000 passes
    await expect(
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          999,
          iface.encodeFunctionData(fn),
          0,
        ),
    ).to.not.be.revert(ethers);

    // 1000 >= 1000 fails
    await expect(
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          1000,
          iface.encodeFunctionData(fn),
          0,
        ),
    )
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ParameterGreaterThanAllowed,
        0n,
        anyValue,
      );
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupOneParamSigned);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.SignedIntLessThan,
              compValue: defaultAbiCoder.encode(["int256"], [100]),
            },
          ],
        }),
      );

      await expect(invoke(200))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterGreaterThanAllowed,
          1, // SignedIntLessThan node at BFS index 1
          anyValue,
        );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupOneParamSigned);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.SignedIntLessThan,
              compValue: defaultAbiCoder.encode(["int256"], [100]),
            },
          ],
        }),
      );

      await expect(invoke(200))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterGreaterThanAllowed,
          anyValue,
          4, // calldataOffset: parameter starts at byte 4
        );
    });
  });

  describe("integrity", () => {
    it("reverts UnsuitableParameterType for invalid encodings", async () => {
      const { roles, evaluator } = await loadFixture(setupTestContract);

      for (const encoding of [
        Encoding.None,
        Encoding.Dynamic,
        Encoding.Tuple,
        Encoding.Array,
        Encoding.AbiEncoded,
      ]) {
        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.SignedIntLessThan,
              compValue: defaultAbiCoder.encode(["int256"], [100]),
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableParameterType");
      }
    });

    it("reverts UnsuitableCompValue when compValue is not 32 bytes", async () => {
      const { roles, evaluator } = await loadFixture(setupTestContract);

      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.SignedIntLessThan,
            compValue: "0x0000", // Not 32 bytes
          },
        ]),
      ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
    });

    it("reverts LeafNodeCannotHaveChildren when SignedIntLessThan has children", async () => {
      const { roles, evaluator } = await loadFixture(setupTestContract);

      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.SignedIntLessThan,
            compValue: defaultAbiCoder.encode(["int256"], [100]),
          },
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithCustomError(evaluator, "LeafNodeCannotHaveChildren");
    });
  });
});
