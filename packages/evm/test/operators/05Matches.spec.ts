import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { AbiCoder, Interface, hexlify, randomBytes, concat } from "ethers";

import { network } from "hardhat";

import { createSetup } from "../setup.js";
import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
} from "../utils.js";

const abiCoder = AbiCoder.defaultAbiCoder();

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupOneParam, setupTwoParams, setupDynamicParam } =
  createSetup(connection);

describe("Operator - Matches", () => {
  after(async () => {
    await connection.close();
  });

  describe("prefix skipping", () => {
    it("skips 10 bytes offset before decoding child", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Matches with AbiEncoded that skips 10 bytes (0x000a) but does NOT match them
      // compValue length is 2 => only configuration, no match bytes
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x000a", // 10 bytes offset
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Send payload with 10 bytes of random junk + encoded param
      // The junk should be skipped, not matched.
      const junkHeader = hexlify(randomBytes(10));
      const paramData = abiCoder.encode(["uint256"], [42]).slice(2); // remove 0x
      const correctPayload = junkHeader + paramData;

      await expect(invoke(correctPayload)).to.not.be.revert(ethers);

      // Ensure that actual logic checks the param (42)
      const wrongParamPayload =
        junkHeader + abiCoder.encode(["uint256"], [99]).slice(2);
      await expect(invoke(wrongParamPayload))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          2, // EqualTo node
          anyValue,
        );
    });
  });
  describe("prefix validation", () => {
    it("validates 4-byte prefix (shift 4)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Matches with 4-byte prefix (common selector size)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef", // 2 bytes length + 4 bytes prefix
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Correct 4-byte prefix + valid param passes
      const correctPayload =
        "0xdeadbeef" + abiCoder.encode(["uint256"], [42]).slice(2);
      await expect(invoke(correctPayload)).to.not.be.revert(ethers);

      // Wrong 4-byte prefix fails
      const wrongPayload =
        "0xcafebabe" + abiCoder.encode(["uint256"], [42]).slice(2);
      await expect(invoke(wrongPayload))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.LeadingBytesNotAMatch,
          1, // Matches node with prefix
          anyValue,
        );
    });

    it("validates 4-byte prefix at the former 2^60 false-rejection boundary", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Regression: the prefix comparison must only cover the N prefix
      // bytes. With the old 28-bit shift, 2^60 leaked into the comparison
      // window and caused a false LeadingBytesNotAMatch rejection.
      const bigValue = 2n ** 60n;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef", // 2 bytes length + 4 bytes prefix
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [bigValue]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Correct prefix + large param value passes
      const payload =
        "0xdeadbeef" + abiCoder.encode(["uint256"], [bigValue]).slice(2);
      await expect(invoke(payload)).to.not.be.revert(ethers);

      // Wrong prefix still fails with LeadingBytesNotAMatch
      const wrongPayload =
        "0xcafebabe" + abiCoder.encode(["uint256"], [bigValue]).slice(2);
      await expect(invoke(wrongPayload))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.LeadingBytesNotAMatch,
          1, // Matches node with prefix
          anyValue,
        );
    });

    it("skips prefix check when compValue is empty (shift 0)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Matches with empty compValue - no prefix check
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0000", // 2 bytes length (0) = no prefix to check
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // Wrong param value fails with ParameterNotAllowed, not LeadingBytesNotAMatch
      const payload = abiCoder.encode(["uint256"], [999]);
      await expect(invoke(payload))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          2, // EqualTo node
          anyValue,
        );
    });

    it("validates 10-byte prefix (shift 10)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      const prefix10 = hexlify(randomBytes(10));

      // Matches with 10-byte prefix
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: concat(["0x000a", prefix10]), // 2 bytes length + 10 bytes prefix
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [123]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Correct 10-byte prefix + valid param passes
      const correctPayload =
        prefix10 + abiCoder.encode(["uint256"], [123]).slice(2);
      await expect(invoke(correctPayload)).to.not.be.revert(ethers);

      // Wrong 10-byte prefix fails with LeadingBytesNotAMatch
      const wrongPrefix10 = hexlify(randomBytes(10));
      const wrongPrefixPayload =
        wrongPrefix10 + abiCoder.encode(["uint256"], [123]).slice(2);
      await expect(invoke(wrongPrefixPayload))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.LeadingBytesNotAMatch,
          1, // Matches node with prefix
          anyValue,
        );

      // Correct prefix + wrong param fails with ParameterNotAllowed
      const wrongParamPayload =
        prefix10 + abiCoder.encode(["uint256"], [999]).slice(2);
      await expect(invoke(wrongParamPayload))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          2, // EqualTo node
          anyValue,
        );
    });

    it("validates 31-byte prefix (shift 31)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      const prefix31 = hexlify(randomBytes(31));

      // Matches with 31-byte prefix
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: concat(["0x001f", prefix31]), // 2 bytes length + 31 bytes prefix
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [456]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // Correct 31-byte prefix + valid param passes
      const correctPayload =
        prefix31 + abiCoder.encode(["uint256"], [456]).slice(2);
      await expect(invoke(correctPayload)).to.not.be.revert(ethers);

      // Wrong 31-byte prefix fails
      const wrongPrefix31 = hexlify(randomBytes(31));
      const wrongPayload =
        wrongPrefix31 + abiCoder.encode(["uint256"], [456]).slice(2);
      await expect(invoke(wrongPayload))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.LeadingBytesNotAMatch,
          1, // Matches node with prefix
          anyValue,
        );
    });
  });

  describe("parameter routing", () => {
    it("routes decoded parameters to corresponding children", async () => {
      const iface = new Interface(["function fn(uint256,uint256,uint256)"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      // Matches routes each param to its corresponding child
      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [100]),
            },
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [200]),
            },
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [300]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // All params match - passes
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [100, 200, 300]),
            0,
          ),
      ).to.not.be.revert(ethers);

      // First param wrong - fails
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [999, 200, 300]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          1, // First EqualTo node
          anyValue,
        );

      // Second param wrong - fails
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [100, 999, 300]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          2, // Second EqualTo node
          anyValue,
        );

      // Third param wrong - fails
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [100, 200, 999]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          3, // Third EqualTo node
          anyValue,
        );
    });

    it("passes empty payload to non-structural children", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            // Structural: Matches checks param
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
              ],
            },
            // Non-structural: checks ether value (sibling of Matches)
            {
              paramType: Encoding.EtherValue,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [100]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Correct param + correct ether
      await expect(invoke(42, { value: 100 })).to.not.be.revert(ethers);

      // Correct param + wrong ether
      await expect(invoke(42, { value: 999 }))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          2, // EtherValue EqualTo node (BFS: And=0, Matches=1, EtherValue=2, Static=3)
          anyValue,
        );
    });

    it("accumulates consumptions across children", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const allowanceKey =
        "0x000000000000000000000000000000000000000000000000000000000000abcd";

      // Set up allowance of 100
      await roles.setAllowance(allowanceKey, 100, 0, 0, 0, 0);

      // Matches with two children consuming from same allowance
      await allowFunction(
        flattenCondition({
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
              operator: Operator.WithinAllowance,
              compValue: allowanceKey,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // First call: 30 + 20 = 50 consumed
      await expect(invoke(30, 20)).to.not.be.revert(ethers);

      // Verify consumption was accumulated
      const { balance } = await roles.accruedAllowance(allowanceKey);
      expect(balance).to.equal(50);

      // Second call: 30 + 30 = 60, but only 50 remaining
      await expect(invoke(30, 30))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          2, // Second WithinAllowance node
          anyValue,
        );
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Pass,
            },
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [42]),
            },
          ],
        }),
      );

      await expect(invoke(100, 99))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          2, // EqualTo child node at BFS index 2
          anyValue,
        );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Pass,
            },
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [42]),
            },
          ],
        }),
      );

      await expect(invoke(100, 99))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          anyValue,
          36, // payloadLocation: second param starts at byte 36 (4 + 32)
        );
    });
  });

  describe("Tuple traversal", () => {
    it("passes when all tuple children match", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface(["function fn((uint256,uint256))"]);
      const fn = iface.getFunction("fn")!;

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [200]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[100, 200]]),
            0,
          ),
      ).to.not.be.revert(ethers);
    });

    it("reverts CalldataOverflow when tuple head is truncated", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const selector = "0xaabbccdd";

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [0]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [0]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Only 32 bytes but tuple needs 64
      const truncatedData = selector + "00".repeat(32);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, truncatedData, 0),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CalldataOverflow,
          anyValue,
          anyValue,
        );
    });

    it("reverts CalldataOverflow when inline element exceeds bounds", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const selector = "0xaabbccdd";

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [0]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [0]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 48 bytes - first element OK, second element truncated
      const truncatedData = selector + "00".repeat(48);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, truncatedData, 0),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CalldataOverflow,
          anyValue,
          anyValue,
        );
    });

    it("reverts ParameterNotAllowed when tuple child value mismatches", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface(["function fn((uint256,uint256))"]);
      const fn = iface.getFunction("fn")!;

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [200]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[100, 999]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          anyValue,
          anyValue,
        );
    });
  });

  describe("Array traversal", () => {
    it("reverts CalldataOverflow when array length slot is truncated", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const selector = "0xaabbccdd";

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.Matches,
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Pointer to offset 32, but only 16 bytes at that location
      const truncatedData =
        selector +
        "0000000000000000000000000000000000000000000000000000000000000020" +
        "00".repeat(16);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, truncatedData, 0),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CalldataOverflow,
          anyValue,
          anyValue,
        );
    });

    it("reverts CalldataOverflow when element exceeds bounds", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const selector = "0xaabbccdd";

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [0]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [0]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [0]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Array claims 3 elements but only 2 slots of data provided
      const truncatedData =
        selector +
        "0000000000000000000000000000000000000000000000000000000000000020" +
        "0000000000000000000000000000000000000000000000000000000000000003" +
        "00".repeat(64);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, truncatedData, 0),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CalldataOverflow,
          anyValue,
          anyValue,
        );
    });

    it("reverts with ParameterNotAMatch when array shorter than expected", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface(["function fn(uint256[])"]);
      const fn = iface.getFunction("fn")!;

      // Condition expects exactly 2 elements
      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [200]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Array with only 1 element - expects 2
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[100]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAMatch,
          anyValue,
          anyValue,
        );
    });

    it("reverts with ParameterNotAMatch when array longer than expected", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface(["function fn(uint256[])"]);
      const fn = iface.getFunction("fn")!;

      // Condition expects exactly 2 elements
      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [200]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Array with 3 elements - first two match, but third element exceeds condition count
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[100, 200, 300]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAMatch,
          anyValue,
          anyValue,
        );
    });

    it("reverts with ParameterNotAllowed when one item does not match", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface(["function fn(uint256[])"]);
      const fn = iface.getFunction("fn")!;

      // Condition expects exactly 2 elements with specific values
      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [200]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Array with correct length but wrong value for second element
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[100, 999]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 3, anyValue);
    });
  });

  describe("AbiEncoded traversal", () => {
    it("passes when nested AbiEncoded matches", async () => {
      const { allowFunction, invoke } = await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef",
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      const payload =
        "0xdeadbeef" + abiCoder.encode(["uint256"], [42]).slice(2);
      await expect(invoke(payload)).to.not.be.revert(ethers);
    });

    it("reverts CalldataOverflow when nested payload is truncated", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef",
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [0]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 4-byte selector + only 16 bytes (need 32)
      const truncatedPayload = "0xdeadbeef" + "00".repeat(16);
      await expect(invoke(truncatedPayload))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CalldataOverflow,
          anyValue,
          anyValue,
        );
    });

    it("reverts LeadingBytesNotAMatch when prefix does not match", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef",
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      const wrongPrefixPayload =
        "0xcafebabe" + abiCoder.encode(["uint256"], [42]).slice(2);
      await expect(invoke(wrongPrefixPayload))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.LeadingBytesNotAMatch,
          anyValue,
          anyValue,
        );
    });

    it("reverts ParameterNotAllowed when decoded child mismatches", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004deadbeef",
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      const wrongValuePayload =
        "0xdeadbeef" + abiCoder.encode(["uint256"], [999]).slice(2);
      await expect(invoke(wrongValuePayload))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          anyValue,
          anyValue,
        );
    });
  });

  describe("Or branches", () => {
    it("passes when one branch succeeds", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface(["function fn(uint256)"]);
      const fn = iface.getFunction("fn")!;

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
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
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [200]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // First branch matches
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [100]),
            0,
          ),
      ).to.not.be.revert(ethers);

      // Second branch matches
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [200]),
            0,
          ),
      ).to.not.be.revert(ethers);
    });

    it("passes when one branch overflows and other succeeds", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.Or,
              children: [
                // Branch 1: expects 2 static params (will overflow with 1)
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000",
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
                // Branch 2: expects 1 static param (will succeed)
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000",
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Single uint256 - first branch overflows, second succeeds
      const payload = abiCoder.encode(["uint256"], [42]);
      await expect(invoke(payload)).to.not.be.revert(ethers);
    });

    it("reverts OrViolation when all branches fail validation", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const iface = new Interface(["function fn(uint256)"]);
      const fn = iface.getFunction("fn")!;

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
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
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [200]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Neither branch matches
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [999]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.OrViolation, anyValue, anyValue);
    });

    it("reverts OrViolation when all branches overflow", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.Or,
              children: [
                // Branch 1: expects 1 static param
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000",
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: abiCoder.encode(["uint256"], [0]),
                    },
                  ],
                },
                // Branch 2: expects 2 static params
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000",
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: abiCoder.encode(["uint256"], [0]),
                    },
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
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

      // Empty bytes - both branches will overflow
      const emptyPayload = "0x";
      await expect(invoke(emptyPayload))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.OrViolation, anyValue, anyValue);
    });
  });

  describe("integrity", () => {
    it("reverts UnsuitableParameterType for invalid encodings", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      for (const encoding of [
        Encoding.None,
        Encoding.Static,
        Encoding.Dynamic,
        Encoding.EtherValue,
      ]) {
        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.Matches,
              compValue: "0x",
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "UnsuitableParameterType");
      }
    });

    describe("compValue", () => {
      it("only AbiEncoded accepts non-empty compValue", async () => {
        const { roles, allowTarget } = await loadFixture(setupTestContract);

        // All valid Matches encodings except AbiEncoded
        for (const encoding of [Encoding.Tuple, Encoding.Array]) {
          await expect(
            allowTarget([
              {
                parent: 0,
                paramType: encoding,
                operator: Operator.Matches,
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
        }
      });

      it("reverts UnsuitableCompValue when AbiEncoded Matches has 1 byte compValue", async () => {
        const { roles, allowTarget } = await loadFixture(setupTestContract);

        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x04", // 1 byte - invalid (must be 0, 2, or 2+N)
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

      it("reverts UnsuitableCompValue when AbiEncoded Matches compValue exceeds 34 bytes", async () => {
        const { roles, allowTarget } = await loadFixture(setupTestContract);

        // 35 bytes = 2 + 33, but N must be <= 32
        const compValue = "0x" + "00".repeat(35);

        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue,
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

    it("requires at least one structural child", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      const allowanceKey = hexlify(randomBytes(32));

      // Tuple and Array require structural children (AbiEncoded does not)
      for (const encoding of [
        Encoding.Tuple,
        Encoding.Array,
        Encoding.AbiEncoded,
      ]) {
        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x",
            },
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.Matches,
              compValue: "0x",
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "UnsuitableChildCount");

        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x",
            },
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.Matches,
              compValue: "0x",
            },
            {
              // Non-structural child - should not count as structural
              parent: 1,
              paramType: Encoding.None,
              operator: Operator.CallWithinAllowance,
              compValue: allowanceKey,
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "UnsuitableChildCount");
      }
    });
  });
});
