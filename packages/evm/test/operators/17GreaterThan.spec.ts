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
} from "../utils.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupOneParam = setupFn("function fn(uint256)");
const setupDynamicParam = setupFn("function fn(bytes)");

describe("Operator - GreaterThan", () => {
  after(async () => {
    await connection.close();
  });

  it("passes when value > compValue", async () => {
    const { allowFunction, invoke } = await loadFixture(setupOneParam);

    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.GreaterThan,
            compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
              100n,
            ]),
          },
        ],
      }),
      ExecutionOptions.None,
    );

    // 101 > 100 passes
    await invoke(101n);
  });

  it("fails when value <= compValue", async () => {
    const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

    await allowFunction(
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.GreaterThan,
            compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
              100n,
            ]),
          },
        ],
      }),
      ExecutionOptions.None,
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

  it("integrates with Slice operator", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupDynamicParam);

    // Slice 4 bytes at offset 0, then GreaterThan comparison
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
                operator: Operator.GreaterThan,
                compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                  100n,
                ]),
              },
            ],
          },
        ],
      }),
      ExecutionOptions.None,
    );

    // 0x00000065 = 101 > 100 passes
    await invoke("0x00000065");

    // 0x00000064 = 100 <= 100 fails
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke("0x00000064"),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ParameterLessThanAllowed, 2n, anyValue],
    );
  });

  it("compares ether value (msg.value)", async () => {
    const abi = parseAbi(["function fn()"]);
    const selector = toFunctionSelector(abi[0]);
    const { roles, member, testContractAddress, roleKey } =
      await loadFixture(setupTestContract);

    // GreaterThan on EtherValue: msg.value must be > 1000 wei
    await roles.write.allowFunction([
      roleKey,
      testContractAddress,
      selector,
      flattenCondition({
        paramType: Encoding.EtherValue,
        operator: Operator.GreaterThan,
        compValue: encodeAbiParameters(parseAbiParameters("uint256"), [1000n]),
      }),
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
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.GreaterThan,
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                100n,
              ]),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(50n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterLessThanAllowed,
          1n, // GreaterThan node at BFS index 1
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
              paramType: Encoding.Static,
              operator: Operator.GreaterThan,
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                100n,
              ]),
            },
          ],
        }),
        ExecutionOptions.None,
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
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      for (const encoding of [
        Encoding.None,
        Encoding.Dynamic,
        Encoding.Tuple,
        Encoding.Array,
        Encoding.AbiEncoded,
      ]) {
        await viem.assertions.revertWithCustomError(
          allowTarget([
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.GreaterThan,
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
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
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      await viem.assertions.revertWithCustomError(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.GreaterThan,
            compValue: "0x0000", // Not 32 bytes
          },
        ]),
        evaluator,
        "UnsuitableCompValue",
      );
    });

    it("reverts LeafNodeCannotHaveChildren when GreaterThan has children", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      await viem.assertions.revertWithCustomError(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.GreaterThan,
            compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
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
