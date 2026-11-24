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

describe("Operator - SignedIntGreaterThan", () => {
  after(async () => {
    await connection.close();
  });

  it("passes when signed value > compValue", async () => {
    const { allowFunction, invoke } = await loadFixture(setupOneParamSigned);

    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.SignedIntGreaterThan,
            compValue: encodeAbiParameters(parseAbiParameters("int256"), [
              100n,
            ]),
          },
        ],
      }),
    );

    // 101 > 100 passes
    await invoke(101n);
  });

  it("fails when signed value <= compValue", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupOneParamSigned);

    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.SignedIntGreaterThan,
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
      [ConditionViolationStatus.ParameterLessThanAllowed, 1n, anyValue],
    );

    // 99 < 100 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(99n),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterLessThanAllowed, 1n, anyValue],
    );
  });

  it("handles negative numbers correctly", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupOneParamSigned);

    // compValue = -50, so value must be > -50
    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.SignedIntGreaterThan,
            compValue: encodeAbiParameters(parseAbiParameters("int256"), [
              -50n,
            ]),
          },
        ],
      }),
    );

    // -49 > -50 passes
    await invoke(-49n);

    // 0 > -50 passes
    await invoke(0n);

    // -50 == -50 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(-50n),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterLessThanAllowed, 1n, anyValue],
    );

    // -51 < -50 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(-51n),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterLessThanAllowed, 1n, anyValue],
    );
  });

  it("integrates with Slice operator", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupDynamicParam);

    // 1. Slice 4 bytes at offset 0, then SignedIntGreaterThan 0
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
                operator: Operator.SignedIntGreaterThan,
                compValue: encodeAbiParameters(parseAbiParameters("int256"), [
                  0n,
                ]),
              },
            ],
          },
        ],
      }),
    );

    // 0x00000001 = 1 > 0 passes
    await invoke("0x00000001");

    // 0x00000000 = 0 <= 0 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke("0x00000000"),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterLessThanAllowed, 2n, anyValue],
    );

    // 0x7fffffff = int32 max > 0 passes
    await invoke("0x7fffffff");

    // 0xffffffff = -1 <= 0 fails (the window is sign-extended)
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke("0xffffffff"),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterLessThanAllowed, 2n, anyValue],
    );

    // 0x80000000 = int32 min <= 0 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke("0x80000000"),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterLessThanAllowed, 2n, anyValue],
    );

    // 2. Slice 32 bytes (full int256) at offset 0, then SignedIntGreaterThan -100
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
                operator: Operator.SignedIntGreaterThan,
                compValue: encodeAbiParameters(parseAbiParameters("int256"), [
                  -100n,
                ]),
              },
            ],
          },
        ],
      }),
    );

    // -50 (32 bytes) > -100 -> Pass
    const neg50 = encodePacked(["int256"], [-50n]);
    await invoke(neg50);

    // -100 (32 bytes) > -100 -> Fail (Equal)
    const neg100 = encodePacked(["int256"], [-100n]);
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(neg100),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterLessThanAllowed, 2n, anyValue],
    );

    // -101 (32 bytes) > -100 -> Fail (Less)
    const neg101 = encodePacked(["int256"], [-101n]);
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(neg101),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterLessThanAllowed, 2n, anyValue],
    );

    // 3. Slice 4 bytes (packed int32) at offset 0, then SignedIntGreaterThan -100
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
                operator: Operator.SignedIntGreaterThan,
                compValue: encodeAbiParameters(parseAbiParameters("int256"), [
                  -100n,
                ]),
              },
            ],
          },
        ],
      }),
    );

    // -50 (4 bytes) > -100 -> Pass
    await invoke(encodePacked(["int32"], [-50]));

    // 50 (4 bytes) > -100 -> Pass
    await invoke(encodePacked(["int32"], [50]));

    // -100 (4 bytes) > -100 -> Fail (Equal)
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(encodePacked(["int32"], [-100])),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterLessThanAllowed, 2n, anyValue],
    );

    // -101 (4 bytes) > -100 -> Fail (Less)
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(encodePacked(["int32"], [-101])),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterLessThanAllowed, 2n, anyValue],
    );
  });

  it("compares ether value (msg.value)", async () => {
    const { roles, member, testContractAddress, roleKey } =
      await loadFixture(setupTestContract);
    const abi = parseAbi(["function fn()"]);
    const selector = toFunctionSelector(abi[0]);

    // SignedIntGreaterThan on EtherValue: msg.value must be > 1000 wei
    const packed = await packConditions(
      roles,
      flattenCondition({
        paramType: Encoding.EtherValue,
        operator: Operator.SignedIntGreaterThan,
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

    // 1001 > 1000 passes
    await roles.write.execTransactionFromModule(
      [
        testContractAddress,
        1001n,
        encodeFunctionData({ abi, functionName: "fn" }),
        0,
      ],
      { account: member.account },
    );

    // 1000 <= 1000 fails
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
      [ConditionViolationStatus.ParameterLessThanAllowed, 0n, anyValue],
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
              operator: Operator.SignedIntGreaterThan,
              compValue: encodeAbiParameters(parseAbiParameters("int256"), [
                100n,
              ]),
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(50n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterLessThanAllowed,
          1n, // SignedIntGreaterThan node at BFS index 1
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
              operator: Operator.SignedIntGreaterThan,
              compValue: encodeAbiParameters(parseAbiParameters("int256"), [
                100n,
              ]),
            },
          ],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(50n),
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
              operator: Operator.SignedIntGreaterThan,
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
            operator: Operator.SignedIntGreaterThan,
            compValue: "0x0000", // Not 32 bytes
          },
        ]),
        evaluator,
        "UnsuitableCompValue",
      );
    });

    it("reverts LeafNodeCannotHaveChildren when SignedIntGreaterThan has children", async () => {
      const { roles, evaluator } = await loadFixture(setupTestContract);

      await viem.assertions.revertWithCustomError(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.SignedIntGreaterThan,
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
