import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { AbiCoder, Interface, hexlify } from "ethers";

import { network } from "hardhat";

import { toFlatNodes } from "../../../sdk/src/main/condition/checkStored.js";
import { packConditions as sdkPackConditions } from "../../../sdk/src/main/condition/packConditions.js";
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

describe("AbiLocation", () => {
  after(async () => {
    await connection.close();
  });

  // ───────────────────────────────────────────────
  // Parent: Tuple
  // ───────────────────────────────────────────────
  describe("Parent: Tuple", () => {
    it("T→S inline: f((uint256))", async () => {
      const iface = new Interface(["function fn((uint256))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [42];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(uint256)"], [target]),
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[999]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("T→D pointer: f((uint256, bytes))", async () => {
      const iface = new Interface(["function fn((uint256, bytes))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [42, "0xdeadbeef"];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(uint256,bytes)"], [target]),
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Dynamic, operator: Operator.Pass },
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[42, "0xaa"]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("T→T inline: f(((uint256, uint256), uint256))", async () => {
      const iface = new Interface([
        "function fn(((uint256, uint256), uint256))",
      ]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [[10, 20], 30];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(
                ["((uint256,uint256),uint256)"],
                [target],
              ),
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
                { paramType: Encoding.Static, operator: Operator.Pass },
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[[99, 20], 30]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("T→T pointer: f((uint256, (uint256, bytes)))", async () => {
      const iface = new Interface(["function fn((uint256, (uint256, bytes)))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [42, [100, "0xaabb"]];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(
                ["(uint256,(uint256,bytes))"],
                [target],
              ),
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                    { paramType: Encoding.Dynamic, operator: Operator.Pass },
                  ],
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[42, [999, "0xaabb"]]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("T→A pointer: f((uint256[]))", async () => {
      const iface = new Interface(["function fn((uint256[]))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [[1, 2, 3]];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(uint256[])"], [target]),
              children: [
                {
                  paramType: Encoding.Array,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[[1, 2, 99]]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("T→E pointer: f((uint256, bytes)) with AbiEncoded child", async () => {
      const iface = new Interface(["function fn((uint256, bytes))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const innerPayload = abiCoder.encode(["uint256"], [777]);
      const target = [42, innerPayload];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(uint256,bytes)"], [target]),
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      const badPayload = abiCoder.encode(["uint256"], [999]);
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[42, badPayload]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("T→N inline: f((uint256, uint256)) with None-wrapped child", async () => {
      const iface = new Interface(["function fn((uint256, uint256))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [10, 20];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(uint256,uint256)"], [target]),
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
                {
                  paramType: Encoding.None,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }) as any,
      );
      const packed = hexlify(sdkPackConditions(flat));
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[10, 99]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("T→N pointer: f((uint256, bytes)) with None-wrapped dynamic child", async () => {
      const iface = new Interface(["function fn((uint256, bytes))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [42, "0xaabbccdd"];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(uint256,bytes)"], [target]),
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
                {
                  paramType: Encoding.None,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Dynamic, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }) as any,
      );
      const packed = hexlify(sdkPackConditions(flat));
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[42, "0xff"]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });
  });

  // ───────────────────────────────────────────────
  // Parent: Array
  // ───────────────────────────────────────────────
  describe("Parent: Array", () => {
    it("A→S inline: f(uint256[])", async () => {
      const iface = new Interface(["function fn(uint256[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [10, 20, 30];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256[]"], [target]),
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[10, 20, 99]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("A→D pointer: f(bytes[])", async () => {
      const iface = new Interface(["function fn(bytes[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = ["0xaabb", "0xccddee"];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["bytes[]"], [target]),
              children: [
                { paramType: Encoding.Dynamic, operator: Operator.Pass },
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [["0xaabb", "0xff"]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("A→T inline: f((uint256, uint256)[])", async () => {
      const iface = new Interface(["function fn((uint256, uint256)[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [
        [1, 2],
        [3, 4],
      ];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(uint256,uint256)[]"], [target]),
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles.connect(member).execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData(fn, [
            [
              [1, 99],
              [3, 4],
            ],
          ]),
          0,
        ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("A→T pointer: f((uint256, bytes)[])", async () => {
      const iface = new Interface(["function fn((uint256, bytes)[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [
        [1, "0xaa"],
        [2, "0xbb"],
      ];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(uint256,bytes)[]"], [target]),
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                    { paramType: Encoding.Dynamic, operator: Operator.Pass },
                  ],
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles.connect(member).execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData(fn, [
            [
              [1, "0xaa"],
              [2, "0xff"],
            ],
          ]),
          0,
        ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("A→A pointer: f(uint256[][])", async () => {
      const iface = new Interface(["function fn(uint256[][])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [
        [1, 2],
        [3, 4, 5],
      ];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256[][]"], [target]),
              children: [
                {
                  paramType: Encoding.Array,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles.connect(member).execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData(fn, [
            [
              [1, 2],
              [3, 4, 99],
            ],
          ]),
          0,
        ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("A→E pointer: f(bytes[]) with AbiEncoded elements", async () => {
      const iface = new Interface(["function fn(bytes[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const elem1 = abiCoder.encode(["uint256"], [100]);
      const elem2 = abiCoder.encode(["uint256"], [200]);
      const target = [elem1, elem2];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["bytes[]"], [target]),
              children: [
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      const badElem = abiCoder.encode(["uint256"], [999]);
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[badElem, elem2]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("A→N inline: f(uint256[]) with None-wrapped element", async () => {
      const iface = new Interface(["function fn(uint256[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [10, 20, 30];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256[]"], [target]),
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }) as any,
      );
      const packed = hexlify(sdkPackConditions(flat));
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[10, 20, 99]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("A→N pointer: f(bytes[]) with None-wrapped dynamic element", async () => {
      const iface = new Interface(["function fn(bytes[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = ["0xaabb", "0xccdd"];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["bytes[]"], [target]),
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.Pass,
                  children: [
                    { paramType: Encoding.Dynamic, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }) as any,
      );
      const packed = hexlify(sdkPackConditions(flat));
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [["0xaabb", "0xff"]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });
  });

  // ───────────────────────────────────────────────
  // Parent: AbiEncoded
  // ───────────────────────────────────────────────
  describe("Parent: AbiEncoded", () => {
    it("E→S inline: f(uint256)", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [12345]),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await expect(invoke(12345)).to.not.be.revert(ethers);

      await expect(invoke(99999))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("E→D pointer: f(bytes)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["bytes"], ["0xdeadbeef"]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke("0xdeadbeef")).to.not.be.revert(ethers);

      await expect(invoke("0xaa"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("E→T inline: f((uint256, uint256))", async () => {
      const iface = new Interface(["function fn((uint256, uint256))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [100, 200];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(uint256,uint256)"], [target]),
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

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
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("E→T pointer: f((uint256, bytes))", async () => {
      const iface = new Interface(["function fn((uint256, bytes))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [50, "0xaabb"];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(uint256,bytes)"], [target]),
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Dynamic, operator: Operator.Pass },
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[50, "0xff"]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("E→A pointer: f(uint256[])", async () => {
      const iface = new Interface(["function fn(uint256[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [5, 10, 15];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256[]"], [target]),
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[5, 10, 99]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("E→E pointer: f(bytes) with nested AbiEncoded payload", async () => {
      const iface = new Interface(["function fn(bytes)"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const innerPayload = abiCoder.encode(["uint256", "uint256"], [100, 200]);

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0000",
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
                { paramType: Encoding.Static, operator: Operator.Pass },
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [innerPayload]),
            0,
          ),
      ).to.not.be.revert(ethers);

      const badPayload = abiCoder.encode(["uint256", "uint256"], [999, 200]);
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [badPayload]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);
    });

    it("E→N inline: f(uint256) with None-wrapped child", async () => {
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
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await expect(invoke(42)).to.not.be.revert(ethers);

      await expect(invoke(99))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);
    });

    it("E→N pointer: f(bytes) with None-wrapped dynamic child", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

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
                  paramType: Encoding.Dynamic,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["bytes"], ["0xaabb"]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke("0xaabb")).to.not.be.revert(ethers);

      await expect(invoke("0xff"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);
    });
  });

  // ───────────────────────────────────────────────
  // Parent: None
  // ───────────────────────────────────────────────
  describe("Parent: None", () => {
    it("N→S inline: f(uint256)", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

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
                  compValue: abiCoder.encode(["uint256"], [42]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await expect(invoke(42)).to.not.be.revert(ethers);

      await expect(invoke(99))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);
    });

    it("N→D pointer: f(bytes)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

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
                  paramType: Encoding.Dynamic,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["bytes"], ["0xaabb"]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke("0xaabb")).to.not.be.revert(ethers);

      await expect(invoke("0xff"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);
    });

    it("N→T inline: f((uint256, uint256))", async () => {
      const iface = new Interface(["function fn((uint256, uint256))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [10, 20];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["(uint256,uint256)"], [target]),
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[10, 99]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);
    });

    it("N→A pointer: f(uint256[])", async () => {
      const iface = new Interface(["function fn(uint256[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const target = [5, 10, 15];

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Array,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256[]"], [target]),
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [target]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[5, 10, 99]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);
    });

    it("N→E pointer: f(bytes) with AbiEncoded payload", async () => {
      const iface = new Interface(["function fn(bytes)"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const innerPayload = abiCoder.encode(["uint256"], [42]);

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000",
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: abiCoder.encode(["uint256"], [42]),
                    },
                  ],
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
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [innerPayload]),
            0,
          ),
      ).to.not.be.revert(ethers);

      const badPayload = abiCoder.encode(["uint256"], [999]);
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [badPayload]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 3, anyValue);
    });

    it("N→N: f(uint256) with double None wrapping", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
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
                      compValue: abiCoder.encode(["uint256"], [42]),
                    },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await expect(invoke(42)).to.not.be.revert(ethers);

      await expect(invoke(99))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 3, anyValue);
    });
  });
});
