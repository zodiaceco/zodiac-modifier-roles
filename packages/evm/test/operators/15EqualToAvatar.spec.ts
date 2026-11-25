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
});
