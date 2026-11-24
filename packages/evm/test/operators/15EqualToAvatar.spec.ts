import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import { network } from "hardhat";
import {
  encodeFunctionData,
  getAddress,
  parseAbi,
  toFunctionSelector,
  toHex,
  zeroAddress,
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
const { setupTestContract } = createSetup(connection);

describe("Operator - EqualToAvatar", () => {
  after(async () => {
    await connection.close();
  });

  describe("comparison logic", () => {
    it("matches when parameter equals the avatar address", async () => {
      const abi = parseAbi(["function fn(address)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const avatar = await roles.read.avatar();

      // EqualToAvatar: parameter must equal the avatar address
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
              operator: Operator.EqualToAvatar,
            },
          ],
        }),
        ExecutionOptions.Both,
      ]);

      // Avatar address passes
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({ abi, functionName: "fn", args: [avatar] }),
          0,
        ],
        { account: member.account },
      );
    });

    it("fails when parameter does not equal the avatar address", async () => {
      const abi = parseAbi(["function fn(address)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      // EqualToAvatar: parameter must equal the avatar address
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
              operator: Operator.EqualToAvatar,
            },
          ],
        }),
        ExecutionOptions.Both,
      ]);

      // Random address fails
      const randomAddress = toHex(randomBytes(20));
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [randomAddress],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );

      // Zero address fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [zeroAddress],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );
    });
  });

  describe("context dynamicism", () => {
    it("matches new avatar address after avatar changes", async () => {
      const abi = parseAbi(["function fn(address)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const originalAvatar = await roles.read.avatar();

      // Set up EqualToAvatar condition
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
              operator: Operator.EqualToAvatar,
            },
          ],
        }),
        ExecutionOptions.Both,
      ]);

      // Original avatar passes
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [originalAvatar],
          }),
          0,
        ],
        { account: member.account },
      );

      // Change the avatar (roles is already connected to owner)
      const newAvatar = getAddress(
        "0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef",
      );
      await roles.write.setAvatar([newAvatar]);

      // Original avatar now fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [originalAvatar],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );

      // New avatar now passes
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({ abi, functionName: "fn", args: [newAvatar] }),
          0,
        ],
        { account: member.account },
      );
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const abi = parseAbi(["function fn(address)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

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
              operator: Operator.EqualToAvatar,
            },
          ],
        }),
        ExecutionOptions.None,
      ]);

      const wrongAddress = toHex(randomBytes(20));
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [wrongAddress],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          1n, // EqualToAvatar node at BFS index 1
          anyValue,
        ],
      );
    });

    it("reports the calldata range of the violation", async () => {
      const abi = parseAbi(["function fn(address)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

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
              operator: Operator.EqualToAvatar,
            },
          ],
        }),
        ExecutionOptions.None,
      ]);

      const wrongAddress = toHex(randomBytes(20));
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [wrongAddress],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
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
        Encoding.EtherValue,
      ]) {
        await viem.assertions.revertWithCustomError(
          allowTarget([
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.EqualToAvatar,
              compValue: "0x",
            },
          ]),
          evaluator,
          "UnsuitableParameterType",
        );
      }
    });

    it("reverts UnsuitableCompValue when compValue is not empty", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      await viem.assertions.revertWithCustomError(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.EqualToAvatar,
            compValue: "0x".padEnd(66, "0") as Hex,
          },
        ]),
        evaluator,
        "UnsuitableCompValue",
      );
    });

    it("reverts LeafNodeCannotHaveChildren when EqualToAvatar has children", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      await viem.assertions.revertWithCustomError(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.EqualToAvatar,
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
        "LeafNodeCannotHaveChildren",
      );
    });
  });
});
