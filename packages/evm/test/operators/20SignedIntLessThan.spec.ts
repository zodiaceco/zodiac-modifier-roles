import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import {
  encodeAbiParameters,
  encodeFunctionData,
  encodePacked,
  parseAbi,
  parseAbiParameters,
  toFunctionSelector,
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

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupDynamicParam = setupFn("function fn(bytes)");
const setupOneParamSigned = setupFn("function fn(int256)");

describe("Operator - SignedIntLessThan", () => {
  after(async () => {
    await connection.close();
  });

  it("passes when signed value < compValue", async () => {
    const { allowFunction, invoke } = await loadFixture(setupOneParamSigned);

    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.SignedIntLessThan,
            compValue: encodeAbiParameters(parseAbiParameters("int256"), [
              100n,
            ]),
          },
        ],
      }),
    );

    // 99 < 100 passes
    await invoke(99n);
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
            compValue: encodeAbiParameters(parseAbiParameters("int256"), [
              100n,
            ]),
          },
        ],
      }),
    );

    // 100 == 100 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(100n),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 1n, anyValue],
    );

    // 101 > 100 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(101n),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 1n, anyValue],
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
            compValue: encodeAbiParameters(parseAbiParameters("int256"), [
              -50n,
            ]),
          },
        ],
      }),
    );

    // -51 < -50 passes
    await invoke(-51n);

    // -100 < -50 passes
    await invoke(-100n);

    // -50 == -50 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(-50n),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 1n, anyValue],
    );

    // -49 > -50 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(-49n),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 1n, anyValue],
    );

    // 0 > -50 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(0n),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 1n, anyValue],
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
            compValue: encodePacked(["uint16", "uint8"], [0, 4]), // shift=0, size=4
            children: [
              {
                paramType: Encoding.Static,
                operator: Operator.SignedIntLessThan,
                compValue: encodeAbiParameters(parseAbiParameters("int256"), [
                  100n,
                ]),
              },
            ],
          },
        ],
      }),
    );

    // 0x00000063 = 99 < 100 passes
    await invoke("0x00000063");

    // 0x00000064 = 100 >= 100 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke("0x00000064"),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 2n, anyValue],
    );

    // 0xffffffff = -1 < 100 passes (the window is sign-extended)
    await invoke("0xffffffff");

    // 0x80000000 = int32 min < 100 passes
    await invoke("0x80000000");

    // 0x7fffffff = int32 max >= 100 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke("0x7fffffff"),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 2n, anyValue],
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
            compValue: encodePacked(["uint16", "uint8"], [0, 32]), // shift=0, size=32
            children: [
              {
                paramType: Encoding.Static,
                operator: Operator.SignedIntLessThan,
                compValue: encodeAbiParameters(parseAbiParameters("int256"), [
                  -100n,
                ]),
              },
            ],
          },
        ],
      }),
    );

    // -150 (32 bytes) < -100 -> Pass
    const neg150 = encodePacked(["int256"], [-150n]);
    await invoke(neg150);

    // -100 (32 bytes) < -100 -> Fail (Equal)
    const neg100 = encodePacked(["int256"], [-100n]);
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(neg100),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 2n, anyValue],
    );

    // -99 (32 bytes) < -100 -> Fail (Greater)
    const neg99 = encodePacked(["int256"], [-99n]);
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(neg99),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 2n, anyValue],
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
            compValue: encodePacked(["uint16", "uint8"], [0, 4]), // shift=0, size=4
            children: [
              {
                paramType: Encoding.Static,
                operator: Operator.SignedIntLessThan,
                compValue: encodeAbiParameters(parseAbiParameters("int256"), [
                  -100n,
                ]),
              },
            ],
          },
        ],
      }),
    );

    // -150 (4 bytes) < -100 -> Pass
    await invoke(encodePacked(["int32"], [-150]));

    // -100 (4 bytes) < -100 -> Fail (Equal)
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(encodePacked(["int32"], [-100])),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 2n, anyValue],
    );

    // -99 (4 bytes) < -100 -> Fail (Greater)
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(encodePacked(["int32"], [-99])),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 2n, anyValue],
    );

    // 50 (4 bytes) < -100 -> Fail (Greater)
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(encodePacked(["int32"], [50])),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 2n, anyValue],
    );
  });

  it("compares ether value (msg.value)", async () => {
    const { roles, member, testContractAddress, roleKey } =
      await loadFixture(setupTestContract);
    const abi = parseAbi(["function fn()"]);
    const selector = toFunctionSelector(abi[0]);

    // SignedIntLessThan on EtherValue: msg.value must be < 1000 wei
    const packed = await packConditions(
      roles,
      flattenCondition({
        paramType: Encoding.EtherValue,
        operator: Operator.SignedIntLessThan,
        compValue: encodeAbiParameters(parseAbiParameters("int256"), [1000n]),
      }),
    );
    await roles.write.allowFunctionPacked([
      roleKey,
      testContractAddress,
      selector,
      packed,
      ExecutionOptions.Send,
    ]);

    // 999 < 1000 passes
    await roles.write.execTransactionFromModule(
      [
        testContractAddress,
        999n,
        encodeFunctionData({ abi, functionName: "fn" }),
        0,
      ],
      { account: member.account },
    );

    // 1000 >= 1000 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      roles.write.execTransactionFromModule(
        [
          testContractAddress,
          1000n,
          encodeFunctionData({ abi, functionName: "fn" }),
          0,
        ],
        { account: member.account },
      ),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterGreaterThanAllowed, 0n, anyValue],
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
              compValue: encodeAbiParameters(parseAbiParameters("int256"), [
                100n,
              ]),
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(200n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterGreaterThanAllowed,
          1n, // SignedIntLessThan node at BFS index 1
          anyValue,
        ],
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
              compValue: encodeAbiParameters(parseAbiParameters("int256"), [
                100n,
              ]),
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(200n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterGreaterThanAllowed,
          anyValue,
          4n, // calldataOffset: parameter starts at byte 4
        ],
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
        await viem.assertions.revertWithCustomError(
          packConditions(roles, [
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.SignedIntLessThan,
              compValue: encodeAbiParameters(parseAbiParameters("int256"), [
                100n,
              ]),
            },
          ]),
          evaluator,
          "UnsuitableParameterType",
        );
      }
    });

    it("reverts UnsuitableCompValue when compValue is not 32 bytes", async () => {
      const { roles, evaluator } = await loadFixture(setupTestContract);

      await viem.assertions.revertWithCustomError(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.SignedIntLessThan,
            compValue: "0x0000", // Not 32 bytes
          },
        ]),
        evaluator,
        "UnsuitableCompValue",
      );
    });

    it("reverts LeafNodeCannotHaveChildren when SignedIntLessThan has children", async () => {
      const { roles, evaluator } = await loadFixture(setupTestContract);

      await viem.assertions.revertWithCustomError(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.SignedIntLessThan,
            compValue: encodeAbiParameters(parseAbiParameters("int256"), [
              100n,
            ]),
          },
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
        evaluator,
        "LeafNodeCannotHaveChildren",
      );
    });
  });
});
