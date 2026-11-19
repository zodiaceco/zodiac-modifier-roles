import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { AbiCoder, Interface, solidityPacked, ZeroHash, hexlify } from "ethers";

import { network } from "hardhat";

import { toFlatNodes } from "../../../sdk/src/main/condition/checkStored.js";
import { packConditions } from "../../../sdk/src/main/condition/packConditions.js";
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
const { setupTestContract, setupOneParam, setupDynamicParam, setupArrayParam } =
  createSetup(connection);

describe("Operator - EqualTo", () => {
  after(async () => {
    await connection.close();
  });

  describe("word-like comparison (size <= 32)", () => {
    it("matches a full 32-byte word (e.g. uint256, bytes32)", async () => {
      const { allowFunction, invoke } = await loadFixture(setupOneParam);

      // EqualTo: parameter must equal 12345
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

      // Exact match passes
      await expect(invoke(12345)).to.not.be.revert(ethers);
    });

    it("fails when values differ", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      // EqualTo: parameter must equal 100
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [100]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Different value fails
      await expect(invoke(101))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          1, // EqualTo node
          anyValue,
        );
    });

    it("integrates with Slice operator", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice 4 bytes at offset 4 (skip first 4 bytes), then EqualTo comparison
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: solidityPacked(["uint16", "uint8"], [4, 4]), // shift=4, size=4
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [0xdeadbeef]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // bytes[4:8] = 0xdeadbeef matches (first 4 bytes ignored)
      await expect(invoke("0x00000000deadbeef")).to.not.be.revert(ethers);

      // bytes[4:8] = 0xcafebabe does not match
      await expect(invoke("0x00000000cafebabe"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          2, // EqualTo node under Slice
          anyValue,
        );
    });

    it("compares ether value (msg.value)", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      // EqualTo on EtherValue: msg.value must equal 1000 wei
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
                  operator: Operator.Pass,
                },
              ],
            },
            {
              paramType: Encoding.EtherValue,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [1000]),
            },
          ],
        }),
        ExecutionOptions.Send,
      );

      // Exact ether value passes
      await expect(invoke(42, { value: 1000 })).to.not.be.revert(ethers);

      // Different ether value fails
      await expect(invoke(42, { value: 1001 }))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          2, // EtherValue/EqualTo node: And[0] -> Matches[1], EqualTo[2]
          anyValue,
        );
    });
  });

  describe("hashed comparison (size > 32)", () => {
    it("matches large dynamic data (e.g. large string/bytes) by comparing hash", async () => {
      const iface = new Interface(["function fn(string)"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      // Large string > 32 bytes
      const largeString =
        "This is a string that is definitely longer than 32 bytes and will be hashed for comparison";

      // EqualTo: parameter must equal the large string (compared by hash)
      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["string"], [largeString]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Exact match passes (hash comparison)
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [largeString]),
            0,
          ),
      ).to.not.be.revert(ethers);
    });

    it("matches complex types (e.g. Tuple, Array) by comparing hash", async () => {
      const { allowFunction, invoke } = await loadFixture(setupArrayParam);

      const targetArray = [1, 2, 3, 4, 5];

      // EqualTo on Array: entire array must match (compared by hash)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256[]"], [targetArray]),
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Pass,
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Exact array match passes
      await expect(invoke(targetArray)).to.not.be.revert(ethers);
    });

    it("fails when large dynamic data differs", async () => {
      const iface = new Interface(["function fn(string)"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const largeString =
        "This is a string that is definitely longer than 32 bytes and will be hashed for comparison";

      // EqualTo: parameter must equal the large string
      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["string"], [largeString]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Different large string fails
      const differentString =
        "This is a different string that is also longer than 32 bytes but has different content";
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [differentString]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          1, // EqualTo node
          anyValue,
        );
    });
  });

  describe("dynamic bytes comparison", () => {
    it("matches empty dynamic value", async () => {
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
              compValue: abiCoder.encode(["bytes"], ["0x"]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke("0x")).to.not.be.revert(ethers);

      await expect(invoke("0xaa"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("matches 10-byte dynamic value", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      const bytes10 = "0x00112233445566778899";

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["bytes"], [bytes10]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke(bytes10)).to.not.be.revert(ethers);

      await expect(invoke("0x00112233445566778800"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("matches 32-byte dynamic value", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      const bytes32 = ZeroHash;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["bytes"], [bytes32]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke(bytes32)).to.not.be.revert(ethers);

      await expect(invoke("0x" + "ff".repeat(32)))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("matches 33-byte dynamic value and fails on length mismatch", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      const bytes33 = "0x" + "11".repeat(33);
      const bytes32 = "0x" + "11".repeat(32);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["bytes"], [bytes33]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke(bytes33)).to.not.be.revert(ethers);

      await expect(invoke(bytes32))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("matches 100-byte dynamic value", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // 100 bytes
      const bytes100 =
        "0x" + "00112233445566778899aabbccddeeff".repeat(6) + "00112233";

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["bytes"], [bytes100]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke(bytes100)).to.not.be.revert(ethers);

      await expect(invoke("0x" + "ff".repeat(100)))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });
  });

  describe("array equality", () => {
    describe("flat arrays", () => {
      it("matches uint256[] array", async () => {
        const iface = new Interface(["function fn(uint256[])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [1, 2, 3, 4, 5];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches address[] array", async () => {
        const iface = new Interface(["function fn(address[])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [
          "0x1111111111111111111111111111111111111111",
          "0x2222222222222222222222222222222222222222",
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["address[]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches bytes32[] array", async () => {
        const iface = new Interface(["function fn(bytes32[])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [
          "0x1111111111111111111111111111111111111111111111111111111111111111",
          "0x2222222222222222222222222222222222222222222222222222222222222222",
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["bytes32[]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches empty uint256[] array", async () => {
        const iface = new Interface(["function fn(uint256[])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: number[] = [];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches empty address[] array", async () => {
        const iface = new Interface(["function fn(address[])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: string[] = [];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["address[]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("fails when array elements differ", async () => {
        const iface = new Interface(["function fn(uint256[])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [1, 2, 3];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [[1, 2, 4]]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });

      it("fails when array length differs", async () => {
        const iface = new Interface(["function fn(uint256[])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [1, 2, 3];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                ],
              },
            ],
          }),
          ExecutionOptions.None,
        );

        await expect(
          roles
            .connect(member)
            .execTransactionFromModule(
              testContractAddress,
              0,
              iface.encodeFunctionData(fn, [[1, 2, 3, 4]]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });
    });

    describe("nested arrays (2 levels)", () => {
      it("matches uint256[][] (array of arrays)", async () => {
        const iface = new Interface(["function fn(uint256[][])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [[1, 2], [3, 4, 5], [6]];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[][]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches address[][] (array of arrays)", async () => {
        const iface = new Interface(["function fn(address[][])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [
          [
            "0x1111111111111111111111111111111111111111",
            "0x2222222222222222222222222222222222222222",
          ],
          ["0x3333333333333333333333333333333333333333"],
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["address[][]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches empty outer array uint256[][]", async () => {
        const iface = new Interface(["function fn(uint256[][])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: number[][] = [];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[][]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches array with empty inner arrays [[],[]]", async () => {
        const iface = new Interface(["function fn(uint256[][])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: number[][] = [[], []];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[][]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("fails when nested array differs", async () => {
        const iface = new Interface(["function fn(uint256[][])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [[1, 2], [3]];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[][]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
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
              iface.encodeFunctionData(fn, [[[1, 2], [4]]]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });
    });

    describe("deeply nested arrays (3 levels)", () => {
      it("matches uint256[][][] (3 levels deep)", async () => {
        const iface = new Interface(["function fn(uint256[][][])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [[[1, 2], [3]], [[4, 5, 6]]];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[][][]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches empty 3-level array", async () => {
        const iface = new Interface(["function fn(uint256[][][])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: number[][][] = [];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[][][]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches 3-level array with mixed empty/populated", async () => {
        const iface = new Interface(["function fn(uint256[][][])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [[[]], [[1], []], [[2, 3]]];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[][][]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("fails when deeply nested array differs", async () => {
        const iface = new Interface(["function fn(uint256[][][])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [[[1, 2]], [[3]]];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(["uint256[][][]"], [targetArray]),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
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
              iface.encodeFunctionData(fn, [[[[1, 2]], [[4]]]]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });
    });
  });

  describe("tuple equality", () => {
    describe("flat tuples", () => {
      it("matches (uint256, address) tuple", async () => {
        const iface = new Interface(["function fn((uint256, address))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [100, "0x1111111111111111111111111111111111111111"];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256,address)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches (uint256, address, bytes32) tuple", async () => {
        const iface = new Interface([
          "function fn((uint256, address, bytes32))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          100,
          "0x1111111111111111111111111111111111111111",
          ZeroHash,
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256,address,bytes32)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches (bool, uint8, int256) tuple", async () => {
        const iface = new Interface(["function fn((bool, uint8, int256))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [true, 255, -100];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(bool,uint8,int256)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("fails when tuple field differs", async () => {
        const iface = new Interface(["function fn((uint256, address))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [100, "0x1111111111111111111111111111111111111111"];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256,address)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [
                [101, "0x1111111111111111111111111111111111111111"],
              ]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });

      it("fails when last tuple field differs", async () => {
        const iface = new Interface([
          "function fn((uint256, address, bytes32))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          100,
          "0x1111111111111111111111111111111111111111",
          ZeroHash,
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256,address,bytes32)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [
                [
                  100,
                  "0x1111111111111111111111111111111111111111",
                  "0x2222222222222222222222222222222222222222222222222222222222222222",
                ],
              ]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });
    });

    describe("nested tuples (2 levels)", () => {
      it("matches ((uint256, address), bytes32) - tuple containing tuple", async () => {
        const iface = new Interface([
          "function fn(((uint256, address), bytes32))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [100, "0x1111111111111111111111111111111111111111"],
          ZeroHash,
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["((uint256,address),bytes32)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches (uint256, (address, uint256)) - tuple with nested tuple", async () => {
        const iface = new Interface([
          "function fn((uint256, (address, uint256)))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          100,
          ["0x1111111111111111111111111111111111111111", 200],
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256,(address,uint256))"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches ((uint256, uint256), (address, address))", async () => {
        const iface = new Interface([
          "function fn(((uint256, uint256), (address, address)))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [100, 200],
          [
            "0x1111111111111111111111111111111111111111",
            "0x2222222222222222222222222222222222222222",
          ],
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["((uint256,uint256),(address,address))"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("fails when nested tuple field differs", async () => {
        const iface = new Interface([
          "function fn(((uint256, address), bytes32))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [100, "0x1111111111111111111111111111111111111111"],
          ZeroHash,
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["((uint256,address),bytes32)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [
                [[101, "0x1111111111111111111111111111111111111111"], ZeroHash],
              ]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });
    });

    describe("deeply nested tuples (3 levels)", () => {
      it("matches (((uint256, address), bytes32), uint256)", async () => {
        const iface = new Interface([
          "function fn((((uint256, address), bytes32), uint256))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [[100, "0x1111111111111111111111111111111111111111"], ZeroHash],
          200,
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(((uint256,address),bytes32),uint256)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Tuple,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches (uint256, ((address, uint256), (bool, bytes32)))", async () => {
        const iface = new Interface([
          "function fn((uint256, ((address, uint256), (bool, bytes32))))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          100,
          [
            ["0x1111111111111111111111111111111111111111", 200],
            [true, ZeroHash],
          ],
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256,((address,uint256),(bool,bytes32)))"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Tuple,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                      {
                        paramType: Encoding.Tuple,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("fails when deeply nested tuple differs", async () => {
        const iface = new Interface([
          "function fn((((uint256, address), bytes32), uint256))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [[100, "0x1111111111111111111111111111111111111111"], ZeroHash],
          200,
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(((uint256,address),bytes32),uint256)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Tuple,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [
                [
                  [
                    [101, "0x1111111111111111111111111111111111111111"],
                    ZeroHash,
                  ],
                  200,
                ],
              ]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });
    });
  });

  describe("tuple-array combinations", () => {
    describe("arrays of tuples", () => {
      it("matches (uint256, address)[] - array of tuples", async () => {
        const iface = new Interface(["function fn((uint256, address)[])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [
          [100, "0x1111111111111111111111111111111111111111"],
          [200, "0x2222222222222222222222222222222222222222"],
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256,address)[]"],
                  [targetArray],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches empty (uint256, address)[] array", async () => {
        const iface = new Interface(["function fn((uint256, address)[])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: [number, string][] = [];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256,address)[]"],
                  [targetArray],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches ((uint256, address), bytes32)[] - array of nested tuples", async () => {
        const iface = new Interface([
          "function fn(((uint256, address), bytes32)[])",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [
          [[100, "0x1111111111111111111111111111111111111111"], ZeroHash],
          [[200, "0x2222222222222222222222222222222222222222"], ZeroHash],
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["((uint256,address),bytes32)[]"],
                  [targetArray],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Tuple,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("fails when array of tuples differs", async () => {
        const iface = new Interface(["function fn((uint256, address)[])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [
          [100, "0x1111111111111111111111111111111111111111"],
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256,address)[]"],
                  [targetArray],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
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
              iface.encodeFunctionData(fn, [
                [[101, "0x1111111111111111111111111111111111111111"]],
              ]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });
    });

    describe("tuples containing arrays", () => {
      it("matches (uint256[], address) - tuple with array field", async () => {
        const iface = new Interface(["function fn((uint256[], address))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [1, 2, 3],
          "0x1111111111111111111111111111111111111111",
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256[],address)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches (address, uint256[], bytes32)", async () => {
        const iface = new Interface([
          "function fn((address, uint256[], bytes32))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          "0x1111111111111111111111111111111111111111",
          [1, 2, 3],
          ZeroHash,
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(address,uint256[],bytes32)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches tuple with empty array field", async () => {
        const iface = new Interface(["function fn((uint256[], address))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [number[], string] = [
          [],
          "0x1111111111111111111111111111111111111111",
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256[],address)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("fails when tuple array field differs", async () => {
        const iface = new Interface(["function fn((uint256[], address))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [1, 2, 3],
          "0x1111111111111111111111111111111111111111",
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256[],address)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [
                [[1, 2, 4], "0x1111111111111111111111111111111111111111"],
              ]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });

      it("fails when tuple array field length differs", async () => {
        const iface = new Interface(["function fn((uint256[], address))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [1, 2, 3],
          "0x1111111111111111111111111111111111111111",
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256[],address)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pass,
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [
                [[1, 2, 3, 4], "0x1111111111111111111111111111111111111111"],
              ]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });
    });

    describe("2-level combinations", () => {
      it("matches (uint256[][], address) - tuple with nested array", async () => {
        const iface = new Interface(["function fn((uint256[][], address))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [[1, 2], [3]],
          "0x1111111111111111111111111111111111111111",
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256[][],address)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches ((uint256, address)[]) - array of tuples in tuple", async () => {
        const iface = new Interface(["function fn(((uint256, address)[]))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [
            [100, "0x1111111111111111111111111111111111111111"],
            [200, "0x2222222222222222222222222222222222222222"],
          ],
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["((uint256,address)[])"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Tuple,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches (uint256, address)[][] - nested array of tuples", async () => {
        const iface = new Interface(["function fn((uint256, address)[][])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [
          [[100, "0x1111111111111111111111111111111111111111"]],
          [
            [200, "0x2222222222222222222222222222222222222222"],
            [300, "0x3333333333333333333333333333333333333333"],
          ],
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256,address)[][]"],
                  [targetArray],
                ),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Tuple,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("fails when 2-level combination differs", async () => {
        const iface = new Interface(["function fn((uint256[][], address))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [[1, 2], [3]],
          "0x1111111111111111111111111111111111111111",
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256[][],address)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [
                [[[1, 2], [4]], "0x1111111111111111111111111111111111111111"],
              ]),
              0,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });
    });

    describe("3-level combinations", () => {
      it("matches (((uint256, address), uint256[]), bytes32)", async () => {
        const iface = new Interface([
          "function fn((((uint256, address), uint256[]), bytes32))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [
            [100, "0x1111111111111111111111111111111111111111"],
            [1, 2, 3],
          ],
          ZeroHash,
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(((uint256,address),uint256[]),bytes32)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Tuple,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches ((uint256[], address[]), (bytes32, uint256)[])", async () => {
        const iface = new Interface([
          "function fn(((uint256[], address[]), (bytes32, uint256)[]))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [
            [1, 2],
            [
              "0x1111111111111111111111111111111111111111",
              "0x2222222222222222222222222222222222222222",
            ],
          ],
          [
            [ZeroHash, 100],
            [
              "0x1111111111111111111111111111111111111111111111111111111111111111",
              200,
            ],
          ],
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["((uint256[],address[]),(bytes32,uint256)[])"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Tuple,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches (uint256, address)[][][] - 3-level array of tuples", async () => {
        const iface = new Interface(["function fn((uint256, address)[][][])"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [
          [[[100, "0x1111111111111111111111111111111111111111"]]],
          [
            [[200, "0x2222222222222222222222222222222222222222"]],
            [[300, "0x3333333333333333333333333333333333333333"]],
          ],
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256,address)[][][]"],
                  [targetArray],
                ),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Tuple,
                            operator: Operator.Pass,
                            children: [
                              {
                                paramType: Encoding.Static,
                                operator: Operator.Pass,
                              },
                              {
                                paramType: Encoding.Static,
                                operator: Operator.Pass,
                              },
                            ],
                          },
                        ],
                      },
                    ],
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
              iface.encodeFunctionData(fn, [targetArray]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches tuple with 3-level nested array field", async () => {
        const iface = new Interface(["function fn((uint256[][][], address))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [[[1, 2], [3]], [[4]]],
          "0x1111111111111111111111111111111111111111",
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256[][][],address)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Array,
                            operator: Operator.Pass,
                            children: [
                              {
                                paramType: Encoding.Static,
                                operator: Operator.Pass,
                              },
                            ],
                          },
                        ],
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("matches 3-level combo with empty arrays at each level", async () => {
        const iface = new Interface(["function fn((uint256[][][], address))"]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [number[][][], string] = [
          [[], [[]], [[1], []]],
          "0x1111111111111111111111111111111111111111",
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(uint256[][][],address)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Array,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Array,
                            operator: Operator.Pass,
                            children: [
                              {
                                paramType: Encoding.Static,
                                operator: Operator.Pass,
                              },
                            ],
                          },
                        ],
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
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
              iface.encodeFunctionData(fn, [targetTuple]),
              0,
            ),
        ).to.not.be.revert(ethers);
      });

      it("fails when 3-level combination differs", async () => {
        const iface = new Interface([
          "function fn((((uint256, address), uint256[]), bytes32))",
        ]);
        const fn = iface.getFunction("fn")!;
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple = [
          [
            [100, "0x1111111111111111111111111111111111111111"],
            [1, 2, 3],
          ],
          ZeroHash,
        ];

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
                operator: Operator.EqualTo,
                compValue: abiCoder.encode(
                  ["(((uint256,address),uint256[]),bytes32)"],
                  [targetTuple],
                ),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      {
                        paramType: Encoding.Tuple,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                      {
                        paramType: Encoding.Array,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                    ],
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                ],
              },
            ],
          }),
          ExecutionOptions.Both,
        );

        await expect(
          roles.connect(member).execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [
              [
                [
                  [101, "0x1111111111111111111111111111111111111111"],
                  [1, 2, 3],
                ],
                ZeroHash,
              ],
            ]),
            0,
          ),
        )
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
      });
    });
  });

  describe("EqualTo with And-typed children", () => {
    it("tuple with And(Static, None) child", async () => {
      const iface = new Interface(["function fn((uint256, uint256))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetTuple = [100, 200];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(uint256,uint256)"], [targetTuple]),
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.Pass,
                    },
                    {
                      paramType: Encoding.None,
                      operator: Operator.Pass,
                    },
                  ],
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.Pass,
                },
              ],
            },
          ],
        }) as any,
      );
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        hexlify(packConditions(flat)),
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [targetTuple]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[999, 200]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("dynamic tuple with And(Static, None) child", async () => {
      const iface = new Interface(["function fn((bytes, uint256))"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetTuple = ["0xdeadbeef", 42];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(bytes,uint256)"], [targetTuple]),
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      paramType: Encoding.None,
                      operator: Operator.Pass,
                    },
                    {
                      paramType: Encoding.Dynamic,
                      operator: Operator.Pass,
                    },
                  ],
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.Pass,
                },
              ],
            },
          ],
        }) as any,
      );
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        hexlify(packConditions(flat)),
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [targetTuple]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [["0xdeadbeef", 99]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("AbiEncoded with And(None, Static) child", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.Pass,
            },
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(["uint256"], [12345]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await expect(invoke(12345)).to.not.be.revert(ethers);

      await expect(invoke(99999))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 3, anyValue);
    });

    it("array with And(None, Static) child", async () => {
      const iface = new Interface(["function fn(uint256[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetArray = [10, 20, 30];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256[]"], [targetArray]),
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      paramType: Encoding.None,
                      operator: Operator.Pass,
                    },
                    {
                      paramType: Encoding.Static,
                      operator: Operator.Pass,
                    },
                  ],
                },
              ],
            },
          ],
        }) as any,
      );
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        hexlify(packConditions(flat)),
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [targetArray]),
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

    it("array with And(None, DynamicTuple) child", async () => {
      const iface = new Interface(["function fn((bytes, uint256)[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetArray = [
        ["0xaabb", 1],
        ["0xccdd", 2],
      ];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["(bytes,uint256)[]"], [targetArray]),
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      paramType: Encoding.None,
                      operator: Operator.Pass,
                    },
                    {
                      paramType: Encoding.Tuple,
                      operator: Operator.Pass,
                      children: [
                        {
                          paramType: Encoding.Dynamic,
                          operator: Operator.Pass,
                        },
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                      ],
                    },
                  ],
                },
              ],
            },
          ],
        }) as any,
      );
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        hexlify(packConditions(flat)),
        ExecutionOptions.Both,
      );

      await expect(
        roles.connect(member).execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData(fn, [
            [
              ["0xaabb", 1],
              ["0xccdd", 2],
            ],
          ]),
          0,
        ),
      ).to.not.be.revert(ethers);

      await expect(
        roles.connect(member).execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData(fn, [
            [
              ["0xaabb", 1],
              ["0xccdd", 999],
            ],
          ]),
          0,
        ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("array with Dynamic and AbiEncoded elements", async () => {
      const iface = new Interface(["function fn(bytes[])"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const innerEncoded1 = abiCoder.encode(
        ["uint256", "address"],
        [100, "0x1111111111111111111111111111111111111111"],
      );
      const innerEncoded2 = abiCoder.encode(
        ["uint256", "address"],
        [200, "0x2222222222222222222222222222222222222222"],
      );
      const targetArray = [innerEncoded1, innerEncoded2];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["bytes[]"], [targetArray]),
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      paramType: Encoding.Dynamic,
                      operator: Operator.Pass,
                    },
                    {
                      paramType: Encoding.AbiEncoded,
                      operator: Operator.Pass,
                      children: [
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                      ],
                    },
                  ],
                },
              ],
            },
          ],
        }) as any,
      );
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        hexlify(packConditions(flat)),
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [targetArray]),
            0,
          ),
      ).to.not.be.revert(ethers);

      const badInner = abiCoder.encode(
        ["uint256", "address"],
        [999, "0x1111111111111111111111111111111111111111"],
      );
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[badInner, innerEncoded2]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });

    it("nested tuple - EqualTo on inner tuple", async () => {
      const iface = new Interface([
        "function fn(((uint256, uint256), uint256))",
      ]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const innerTuple = [10, 20];
      const targetTuple = [innerTuple, 300];

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
                  paramType: Encoding.Tuple,
                  operator: Operator.EqualTo,
                  compValue: abiCoder.encode(
                    ["(uint256,uint256)"],
                    [innerTuple],
                  ),
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.Pass,
                    },
                    {
                      paramType: Encoding.Static,
                      operator: Operator.Pass,
                    },
                  ],
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.Pass,
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
            iface.encodeFunctionData(fn, [targetTuple]),
            0,
          ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[[99, 20], 300]]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);
    });

    it("array of AbiEncoded elements - EqualTo on array", async () => {
      const iface = new Interface(["function fn(bytes[], uint256)"]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const innerEncoded1 = abiCoder.encode(
        ["uint256", "bytes"],
        [50, "0xaabbccdd"],
      );
      const innerEncoded2 = abiCoder.encode(
        ["uint256", "bytes"],
        [60, "0xeeff0011"],
      );
      const targetArray = [innerEncoded1, innerEncoded2];
      const targetDynamic = 777;

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["bytes[]"], [targetArray]),
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      paramType: Encoding.Dynamic,
                      operator: Operator.Pass,
                    },
                    {
                      paramType: Encoding.AbiEncoded,
                      operator: Operator.Pass,
                      children: [
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                        {
                          paramType: Encoding.Dynamic,
                          operator: Operator.Pass,
                        },
                      ],
                    },
                  ],
                },
              ],
            },
            {
              paramType: Encoding.Static,
              operator: Operator.Pass,
            },
          ],
        }) as any,
      );
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        hexlify(packConditions(flat)),
        ExecutionOptions.Both,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [targetArray, targetDynamic]),
            0,
          ),
      ).to.not.be.revert(ethers);

      const badInner = abiCoder.encode(
        ["uint256", "bytes"],
        [999, "0xaabbccdd"],
      );
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [
              [badInner, innerEncoded2],
              targetDynamic,
            ]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, anyValue);
    });
  });

  describe("edge cases for complex types", () => {
    it("handles maximum practical nesting depth", async () => {
      const iface = new Interface([
        "function fn((((uint256, address), (bytes32, uint256)), ((bool, uint8), (int256, address))))",
      ]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetTuple = [
        [
          [100, "0x1111111111111111111111111111111111111111"],
          [ZeroHash, 200],
        ],
        [
          [true, 255],
          [-100, "0x2222222222222222222222222222222222222222"],
        ],
      ];

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
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(
                [
                  "(((uint256,address),(bytes32,uint256)),((bool,uint8),(int256,address)))",
                ],
                [targetTuple],
              ),
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Pass,
                  children: [
                    {
                      paramType: Encoding.Tuple,
                      operator: Operator.Pass,
                      children: [
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                      ],
                    },
                    {
                      paramType: Encoding.Tuple,
                      operator: Operator.Pass,
                      children: [
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                      ],
                    },
                  ],
                },
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Pass,
                  children: [
                    {
                      paramType: Encoding.Tuple,
                      operator: Operator.Pass,
                      children: [
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                      ],
                    },
                    {
                      paramType: Encoding.Tuple,
                      operator: Operator.Pass,
                      children: [
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pass,
                        },
                      ],
                    },
                  ],
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
            iface.encodeFunctionData(fn, [targetTuple]),
            0,
          ),
      ).to.not.be.revert(ethers);
    });

    it.skip("handles large condition trees (600 nodes)", async () => {
      // Limited by block gas (100M in hardhat config)
      // 1 AbiEncoded + 1 Tuple + X*(1 Array + 1 Tuple + 4 Static) = 602
      // 2 + 6X = 602 => X = 100 array fields (602 nodes)

      const innerTupleType = "(uint256, uint256, uint256, address)";
      const arrayCount = 100;
      const fields = Array(arrayCount).fill(`${innerTupleType}[]`);
      const outerTupleType = `(${fields.join(", ")})`;

      const iface = new Interface([`function fn(${outerTupleType})`]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, allowTarget } =
        await loadFixture(setupTestContract);

      // Each array has 2 tuples
      const innerTuple = [
        42,
        100,
        200,
        "0x1111111111111111111111111111111111111111",
      ];
      const targetValue = Array(arrayCount).fill([innerTuple, innerTuple]);

      await allowTarget(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode([outerTupleType], [targetValue]),
              children: Array.from({ length: arrayCount }, () => ({
                paramType: Encoding.Array,
                operator: Operator.Pass,
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                    ],
                  },
                ],
              })),
            },
          ],
        }),
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [targetValue]),
            0,
          ),
      ).to.not.be.revert(ethers);
    });

    it("handles tuples with many fields (10+ fields)", async () => {
      const iface = new Interface([
        "function fn((uint256, uint256, uint256, uint256, uint256, uint256, uint256, uint256, uint256, uint256, address))",
      ]);
      const fn = iface.getFunction("fn")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetTuple = [
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        10,
        "0x1111111111111111111111111111111111111111",
      ];

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
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(
                [
                  "(uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,address)",
                ],
                [targetTuple],
              ),
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
                { paramType: Encoding.Static, operator: Operator.Pass },
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
            iface.encodeFunctionData(fn, [targetTuple]),
            0,
          ),
      ).to.not.be.revert(ethers);
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
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [100]),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await expect(invoke(999))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          1, // EqualTo node at BFS index 1
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
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [100]),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await expect(invoke(999))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          anyValue,
          4, // payloadLocation: parameter starts at byte 4 (after selector)
        );
    });
  });

  describe.skip("integrity", () => {
    it("reverts UnsuitableParameterType for invalid encodings", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      for (const encoding of [Encoding.None, Encoding.AbiEncoded]) {
        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.EqualTo,
              compValue: abiCoder.encode(["uint256"], [100]),
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "UnsuitableParameterType");
      }
    });

    it("reverts UnsuitableCompValue when compValue is empty", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      await expect(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.EqualTo,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");
    });
  });
});
