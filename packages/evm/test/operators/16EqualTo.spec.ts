import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import {
  encodeAbiParameters,
  encodeFunctionData,
  encodePacked,
  parseAbi,
  parseAbiParameters,
  toFunctionSelector,
  toHex,
  zeroHash,
  type Abi,
  type Address,
  type Hex,
} from "viem";

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

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupOneParam = setupFn("function fn(uint256)");
const setupDynamicParam = setupFn("function fn(bytes)");
const setupArrayParam = setupFn("function fn(uint256[])");

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
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                12345n,
              ]),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // Exact match passes
      await invoke(12345n);
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
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                100n,
              ]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Different value fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(101n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          1n, // EqualTo node
          anyValue,
        ],
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
              compValue: encodePacked(["uint16", "uint8"], [4, 4]), // shift=4, size=4
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [0xdeadbeefn],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.None,
      );

      // bytes[4:8] = 0xdeadbeef matches (first 4 bytes ignored)
      await invoke("0x00000000deadbeef");

      // bytes[4:8] = 0xcafebabe does not match
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x00000000cafebabe"),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          2n, // EqualTo node under Slice
          anyValue,
        ],
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
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                1000n,
              ]),
            },
          ],
        }),
        ExecutionOptions.Send,
      );

      // Exact ether value passes
      await invoke(42n, { value: 1000n });

      // Different ether value fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(42n, { value: 1001n }),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          2n, // EtherValue/EqualTo node: And[0] -> Matches[1], EqualTo[2]
          anyValue,
        ],
      );
    });
  });

  describe("hashed comparison (size > 32)", () => {
    it("matches large dynamic data (e.g. large string/bytes) by comparing hash", async () => {
      const abi = parseAbi(["function fn(string)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      // Large string > 32 bytes
      const largeString =
        "This is a string that is definitely longer than 32 bytes and will be hashed for comparison";

      // EqualTo: parameter must equal the large string (compared by hash)
      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("string"), [
                largeString,
              ]),
            },
          ],
        }),
        ExecutionOptions.Both,
      ]);

      // Exact match passes (hash comparison)
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [largeString],
          }),
          0,
        ],
        { account: member.account },
      );
    });

    it("matches complex types (e.g. Tuple, Array) by comparing hash", async () => {
      const { allowFunction, invoke } = await loadFixture(setupArrayParam);

      const targetArray = [1n, 2n, 3n, 4n, 5n];

      // EqualTo on Array: entire array must match (compared by hash)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("uint256[]"), [
                targetArray,
              ]),
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
      await invoke(targetArray);
    });

    it("fails when large dynamic data differs", async () => {
      const abi = parseAbi(["function fn(string)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const largeString =
        "This is a string that is definitely longer than 32 bytes and will be hashed for comparison";

      // EqualTo: parameter must equal the large string
      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("string"), [
                largeString,
              ]),
            },
          ],
        }),
        ExecutionOptions.Both,
      ]);

      // Different large string fails
      const differentString =
        "This is a different string that is also longer than 32 bytes but has different content";
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [differentString],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          1n, // EqualTo node
          anyValue,
        ],
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
              compValue: encodeAbiParameters(parseAbiParameters("bytes"), [
                "0x",
              ]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke("0x");

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0xaa"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );
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
              compValue: encodeAbiParameters(parseAbiParameters("bytes"), [
                bytes10,
              ]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke(bytes10);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x00112233445566778800"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );
    });

    it("matches 32-byte dynamic value", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      const bytes32 = zeroHash;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("bytes"), [
                bytes32,
              ]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke(bytes32);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x" + "ff".repeat(32)),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );
    });

    it("matches 33-byte dynamic value and fails on length mismatch", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      const bytes33 = `0x${"11".repeat(33)}` as const;
      const bytes32 = `0x${"11".repeat(32)}` as const;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("bytes"), [
                bytes33,
              ]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke(bytes33);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(bytes32),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );
    });

    it("matches 100-byte dynamic value", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // 100 bytes
      const bytes100 =
        `0x${"00112233445566778899aabbccddeeff".repeat(6)}00112233` as const;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("bytes"), [
                bytes100,
              ]),
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke(bytes100);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x" + "ff".repeat(100)),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, anyValue],
      );
    });
  });

  describe("array equality", () => {
    describe("flat arrays", () => {
      it("matches uint256[] array", async () => {
        const abi = parseAbi(["function fn(uint256[])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [1n, 2n, 3n, 4n, 5n];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[]"),
                  [targetArray],
                ),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches address[] array", async () => {
        const abi = parseAbi(["function fn(address[])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: Address[] = [
          "0x1111111111111111111111111111111111111111",
          "0x2222222222222222222222222222222222222222",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("address[]"),
                  [targetArray],
                ),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches bytes32[] array", async () => {
        const abi = parseAbi(["function fn(bytes32[])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: Hex[] = [
          "0x1111111111111111111111111111111111111111111111111111111111111111",
          "0x2222222222222222222222222222222222222222222222222222222222222222",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("bytes32[]"),
                  [targetArray],
                ),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches empty uint256[] array", async () => {
        const abi = parseAbi(["function fn(uint256[])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: bigint[] = [];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[]"),
                  [targetArray],
                ),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches empty address[] array", async () => {
        const abi = parseAbi(["function fn(address[])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: Address[] = [];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("address[]"),
                  [targetArray],
                ),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("fails when array elements differ", async () => {
        const abi = parseAbi(["function fn(uint256[])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [1n, 2n, 3n];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[]"),
                  [targetArray],
                ),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [[1n, 2n, 4n]],
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

      it("fails when array length differs", async () => {
        const abi = parseAbi(["function fn(uint256[])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [1n, 2n, 3n];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[]"),
                  [targetArray],
                ),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [[1n, 2n, 3n, 4n]],
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

    describe("nested arrays (2 levels)", () => {
      it("matches uint256[][] (array of arrays)", async () => {
        const abi = parseAbi(["function fn(uint256[][])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [[1n, 2n], [3n, 4n, 5n], [6n]];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[][]"),
                  [targetArray],
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
                ],
              },
            ],
          }),
          ExecutionOptions.Both,
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches address[][] (array of arrays)", async () => {
        const abi = parseAbi(["function fn(address[][])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: Address[][] = [
          [
            "0x1111111111111111111111111111111111111111",
            "0x2222222222222222222222222222222222222222",
          ],
          ["0x3333333333333333333333333333333333333333"],
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("address[][]"),
                  [targetArray],
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
                ],
              },
            ],
          }),
          ExecutionOptions.Both,
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches empty outer array uint256[][]", async () => {
        const abi = parseAbi(["function fn(uint256[][])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: bigint[][] = [];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[][]"),
                  [targetArray],
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
                ],
              },
            ],
          }),
          ExecutionOptions.Both,
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches array with empty inner arrays [[],[]]", async () => {
        const abi = parseAbi(["function fn(uint256[][])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: bigint[][] = [[], []];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[][]"),
                  [targetArray],
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
                ],
              },
            ],
          }),
          ExecutionOptions.Both,
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("fails when nested array differs", async () => {
        const abi = parseAbi(["function fn(uint256[][])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [[1n, 2n], [3n]];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[][]"),
                  [targetArray],
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
                ],
              },
            ],
          }),
          ExecutionOptions.Both,
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [[[1n, 2n], [4n]]],
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

    describe("deeply nested arrays (3 levels)", () => {
      it("matches uint256[][][] (3 levels deep)", async () => {
        const abi = parseAbi(["function fn(uint256[][][])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [[[1n, 2n], [3n]], [[4n, 5n, 6n]]];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[][][]"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches empty 3-level array", async () => {
        const abi = parseAbi(["function fn(uint256[][][])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: bigint[][][] = [];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[][][]"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches 3-level array with mixed empty/populated", async () => {
        const abi = parseAbi(["function fn(uint256[][][])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [[[]], [[1n], []], [[2n, 3n]]];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[][][]"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("fails when deeply nested array differs", async () => {
        const abi = parseAbi(["function fn(uint256[][][])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray = [[[1n, 2n]], [[3n]]];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("uint256[][][]"),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [[[[1n, 2n]], [[4n]]]],
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
  });

  describe("tuple equality", () => {
    describe("flat tuples", () => {
      it("matches (uint256, address) tuple", async () => {
        const abi = parseAbi(["function fn((uint256, address))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint, Address] = [
          100n,
          "0x1111111111111111111111111111111111111111",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256,address)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches (uint256, address, bytes32) tuple", async () => {
        const abi = parseAbi(["function fn((uint256, address, bytes32))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint, Address, Hex] = [
          100n,
          "0x1111111111111111111111111111111111111111",
          zeroHash,
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256,address,bytes32)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches (bool, uint8, int256) tuple", async () => {
        const abi = parseAbi(["function fn((bool, uint8, int256))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [boolean, number, bigint] = [true, 255, -100n];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(bool,uint8,int256)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("fails when tuple field differs", async () => {
        const abi = parseAbi(["function fn((uint256, address))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint, Address] = [
          100n,
          "0x1111111111111111111111111111111111111111",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256,address)"),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [[101n, "0x1111111111111111111111111111111111111111"]],
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

      it("fails when last tuple field differs", async () => {
        const abi = parseAbi(["function fn((uint256, address, bytes32))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint, Address, Hex] = [
          100n,
          "0x1111111111111111111111111111111111111111",
          zeroHash,
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256,address,bytes32)"),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [
                  [
                    100n,
                    "0x1111111111111111111111111111111111111111",
                    "0x2222222222222222222222222222222222222222222222222222222222222222",
                  ],
                ],
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

    describe("nested tuples (2 levels)", () => {
      it("matches ((uint256, address), bytes32) - tuple containing tuple", async () => {
        const abi = parseAbi(["function fn(((uint256, address), bytes32))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [[bigint, Address], Hex] = [
          [100n, "0x1111111111111111111111111111111111111111"],
          zeroHash,
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("((uint256,address),bytes32)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches (uint256, (address, uint256)) - tuple with nested tuple", async () => {
        const abi = parseAbi(["function fn((uint256, (address, uint256)))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint, [Address, bigint]] = [
          100n,
          ["0x1111111111111111111111111111111111111111", 200n],
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256,(address,uint256))"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches ((uint256, uint256), (address, address))", async () => {
        const abi = parseAbi([
          "function fn(((uint256, uint256), (address, address)))",
        ]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [[bigint, bigint], [Address, Address]] = [
          [100n, 200n],
          [
            "0x1111111111111111111111111111111111111111",
            "0x2222222222222222222222222222222222222222",
          ],
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("((uint256,uint256),(address,address))"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("fails when nested tuple field differs", async () => {
        const abi = parseAbi(["function fn(((uint256, address), bytes32))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [[bigint, Address], Hex] = [
          [100n, "0x1111111111111111111111111111111111111111"],
          zeroHash,
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("((uint256,address),bytes32)"),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [
                  [
                    [101n, "0x1111111111111111111111111111111111111111"],
                    zeroHash,
                  ],
                ],
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

    describe("deeply nested tuples (3 levels)", () => {
      it("matches (((uint256, address), bytes32), uint256)", async () => {
        const abi = parseAbi([
          "function fn((((uint256, address), bytes32), uint256))",
        ]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [[[bigint, Address], Hex], bigint] = [
          [[100n, "0x1111111111111111111111111111111111111111"], zeroHash],
          200n,
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(((uint256,address),bytes32),uint256)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches (uint256, ((address, uint256), (bool, bytes32)))", async () => {
        const abi = parseAbi([
          "function fn((uint256, ((address, uint256), (bool, bytes32))))",
        ]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint, [[Address, bigint], [boolean, Hex]]] = [
          100n,
          [
            ["0x1111111111111111111111111111111111111111", 200n],
            [true, zeroHash],
          ],
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters(
                    "(uint256,((address,uint256),(bool,bytes32)))",
                  ),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("fails when deeply nested tuple differs", async () => {
        const abi = parseAbi([
          "function fn((((uint256, address), bytes32), uint256))",
        ]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [[[bigint, Address], Hex], bigint] = [
          [[100n, "0x1111111111111111111111111111111111111111"], zeroHash],
          200n,
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(((uint256,address),bytes32),uint256)"),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [
                  [
                    [
                      [101n, "0x1111111111111111111111111111111111111111"],
                      zeroHash,
                    ],
                    200n,
                  ],
                ],
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
  });

  describe("tuple-array combinations", () => {
    describe("arrays of tuples", () => {
      it("matches (uint256, address)[] - array of tuples", async () => {
        const abi = parseAbi(["function fn((uint256, address)[])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: [bigint, Address][] = [
          [100n, "0x1111111111111111111111111111111111111111"],
          [200n, "0x2222222222222222222222222222222222222222"],
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256,address)[]"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches empty (uint256, address)[] array", async () => {
        const abi = parseAbi(["function fn((uint256, address)[])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: [bigint, Address][] = [];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256,address)[]"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches ((uint256, address), bytes32)[] - array of nested tuples", async () => {
        const abi = parseAbi(["function fn(((uint256, address), bytes32)[])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: [[bigint, Address], Hex][] = [
          [[100n, "0x1111111111111111111111111111111111111111"], zeroHash],
          [[200n, "0x2222222222222222222222222222222222222222"], zeroHash],
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("((uint256,address),bytes32)[]"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("fails when array of tuples differs", async () => {
        const abi = parseAbi(["function fn((uint256, address)[])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: [bigint, Address][] = [
          [100n, "0x1111111111111111111111111111111111111111"],
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256,address)[]"),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [[[101n, "0x1111111111111111111111111111111111111111"]]],
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

    describe("tuples containing arrays", () => {
      it("matches (uint256[], address) - tuple with array field", async () => {
        const abi = parseAbi(["function fn((uint256[], address))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint[], Address] = [
          [1n, 2n, 3n],
          "0x1111111111111111111111111111111111111111",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256[],address)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches (address, uint256[], bytes32)", async () => {
        const abi = parseAbi(["function fn((address, uint256[], bytes32))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [Address, bigint[], Hex] = [
          "0x1111111111111111111111111111111111111111",
          [1n, 2n, 3n],
          zeroHash,
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(address,uint256[],bytes32)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches tuple with empty array field", async () => {
        const abi = parseAbi(["function fn((uint256[], address))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint[], Address] = [
          [],
          "0x1111111111111111111111111111111111111111",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256[],address)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("fails when tuple array field differs", async () => {
        const abi = parseAbi(["function fn((uint256[], address))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint[], Address] = [
          [1n, 2n, 3n],
          "0x1111111111111111111111111111111111111111",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256[],address)"),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [
                  [[1n, 2n, 4n], "0x1111111111111111111111111111111111111111"],
                ],
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

      it("fails when tuple array field length differs", async () => {
        const abi = parseAbi(["function fn((uint256[], address))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint[], Address] = [
          [1n, 2n, 3n],
          "0x1111111111111111111111111111111111111111",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256[],address)"),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [
                  [
                    [1n, 2n, 3n, 4n],
                    "0x1111111111111111111111111111111111111111",
                  ],
                ],
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

    describe("2-level combinations", () => {
      it("matches (uint256[][], address) - tuple with nested array", async () => {
        const abi = parseAbi(["function fn((uint256[][], address))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint[][], Address] = [
          [[1n, 2n], [3n]],
          "0x1111111111111111111111111111111111111111",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256[][],address)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches ((uint256, address)[]) - array of tuples in tuple", async () => {
        const abi = parseAbi(["function fn(((uint256, address)[]))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [[bigint, Address][]] = [
          [
            [100n, "0x1111111111111111111111111111111111111111"],
            [200n, "0x2222222222222222222222222222222222222222"],
          ],
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("((uint256,address)[])"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches (uint256, address)[][] - nested array of tuples", async () => {
        const abi = parseAbi(["function fn((uint256, address)[][])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: [bigint, Address][][] = [
          [[100n, "0x1111111111111111111111111111111111111111"]],
          [
            [200n, "0x2222222222222222222222222222222222222222"],
            [300n, "0x3333333333333333333333333333333333333333"],
          ],
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  [
                    {
                      type: "tuple[][]",
                      components: [{ type: "uint256" }, { type: "address" }],
                    },
                  ],
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("fails when 2-level combination differs", async () => {
        const abi = parseAbi(["function fn((uint256[][], address))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint[][], Address] = [
          [[1n, 2n], [3n]],
          "0x1111111111111111111111111111111111111111",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256[][],address)"),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [
                  [
                    [[1n, 2n], [4n]],
                    "0x1111111111111111111111111111111111111111",
                  ],
                ],
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

    describe("3-level combinations", () => {
      it("matches (((uint256, address), uint256[]), bytes32)", async () => {
        const abi = parseAbi([
          "function fn((((uint256, address), uint256[]), bytes32))",
        ]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [[[bigint, Address], bigint[]], Hex] = [
          [
            [100n, "0x1111111111111111111111111111111111111111"],
            [1n, 2n, 3n],
          ],
          zeroHash,
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(((uint256,address),uint256[]),bytes32)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches ((uint256[], address[]), (bytes32, uint256)[])", async () => {
        const abi = parseAbi([
          "function fn(((uint256[], address[]), (bytes32, uint256)[]))",
        ]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [[bigint[], Address[]], [Hex, bigint][]] = [
          [
            [1n, 2n],
            [
              "0x1111111111111111111111111111111111111111",
              "0x2222222222222222222222222222222222222222",
            ],
          ],
          [
            [zeroHash, 100n],
            [
              "0x1111111111111111111111111111111111111111111111111111111111111111",
              200n,
            ],
          ],
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters(
                    "((uint256[],address[]),(bytes32,uint256)[])",
                  ),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches (uint256, address)[][][] - 3-level array of tuples", async () => {
        const abi = parseAbi(["function fn((uint256, address)[][][])"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetArray: [bigint, Address][][][] = [
          [[[100n, "0x1111111111111111111111111111111111111111"]]],
          [
            [[200n, "0x2222222222222222222222222222222222222222"]],
            [[300n, "0x3333333333333333333333333333333333333333"]],
          ],
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Array,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  [
                    {
                      type: "tuple[][][]",
                      components: [{ type: "uint256" }, { type: "address" }],
                    },
                  ],
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetArray],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches tuple with 3-level nested array field", async () => {
        const abi = parseAbi(["function fn((uint256[][][], address))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint[][][], Address] = [
          [[[1n, 2n], [3n]], [[4n]]],
          "0x1111111111111111111111111111111111111111",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256[][][],address)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("matches 3-level combo with empty arrays at each level", async () => {
        const abi = parseAbi(["function fn((uint256[][][], address))"]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [bigint[][][], Address] = [
          [[], [[]], [[1n], []]],
          "0x1111111111111111111111111111111111111111",
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(uint256[][][],address)"),
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
        ]);

        await roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [targetTuple],
            }),
            0,
          ],
          { account: member.account },
        );
      });

      it("fails when 3-level combination differs", async () => {
        const abi = parseAbi([
          "function fn((((uint256, address), uint256[]), bytes32))",
        ]);
        const selector = toFunctionSelector(abi[0]);
        const { roles, member, testContractAddress, roleKey } =
          await loadFixture(setupTestContract);

        const targetTuple: [[[bigint, Address], bigint[]], Hex] = [
          [
            [100n, "0x1111111111111111111111111111111111111111"],
            [1n, 2n, 3n],
          ],
          zeroHash,
        ];

        await roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          flattenCondition({
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.EqualTo,
                compValue: encodeAbiParameters(
                  parseAbiParameters("(((uint256,address),uint256[]),bytes32)"),
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
        ]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionFromModule(
            [
              testContractAddress,
              0n,
              encodeFunctionData({
                abi,
                functionName: "fn",
                args: [
                  [
                    [
                      [101n, "0x1111111111111111111111111111111111111111"],
                      [1n, 2n, 3n],
                    ],
                    zeroHash,
                  ],
                ],
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
  });

  describe("EqualTo with And-typed children", () => {
    it("tuple with And(Static, None) child", async () => {
      const abi = parseAbi(["function fn((uint256, uint256))"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetTuple: [bigint, bigint] = [100n, 200n];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(
                parseAbiParameters("(uint256,uint256)"),
                [targetTuple],
              ),
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
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        toHex(packConditions(flat)),
        ExecutionOptions.Both,
      ]);

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [targetTuple],
          }),
          0,
        ],
        { account: member.account },
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [[999n, 200n]],
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

    it("dynamic tuple with And(Static, None) child", async () => {
      const abi = parseAbi(["function fn((bytes, uint256))"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetTuple: [Hex, bigint] = ["0xdeadbeef", 42n];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(
                parseAbiParameters("(bytes,uint256)"),
                [targetTuple],
              ),
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
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        toHex(packConditions(flat)),
        ExecutionOptions.Both,
      ]);

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [targetTuple],
          }),
          0,
        ],
        { account: member.account },
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [["0xdeadbeef", 99n]],
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
                  compValue: encodeAbiParameters(
                    parseAbiParameters("uint256"),
                    [12345n],
                  ),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await invoke(12345n);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(99999n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 3n, anyValue],
      );
    });

    it("array with And(None, Static) child", async () => {
      const abi = parseAbi(["function fn(uint256[])"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetArray = [10n, 20n, 30n];

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("uint256[]"), [
                targetArray,
              ]),
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
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        toHex(packConditions(flat)),
        ExecutionOptions.Both,
      ]);

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [targetArray],
          }),
          0,
        ],
        { account: member.account },
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [[10n, 20n, 99n]],
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

    it("array with And(None, DynamicTuple) child", async () => {
      const abi = parseAbi(["function fn((bytes, uint256)[])"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetArray: [Hex, bigint][] = [
        ["0xaabb", 1n],
        ["0xccdd", 2n],
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
              compValue: encodeAbiParameters(
                parseAbiParameters("(bytes,uint256)[]"),
                [targetArray],
              ),
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
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        toHex(packConditions(flat)),
        ExecutionOptions.Both,
      ]);

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [
              [
                ["0xaabb", 1n],
                ["0xccdd", 2n],
              ],
            ],
          }),
          0,
        ],
        { account: member.account },
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [
                [
                  ["0xaabb", 1n],
                  ["0xccdd", 999n],
                ],
              ],
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

    it("array with Dynamic and AbiEncoded elements", async () => {
      const abi = parseAbi(["function fn(bytes[])"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const innerEncoded1 = encodeAbiParameters(
        parseAbiParameters("uint256, address"),
        [100n, "0x1111111111111111111111111111111111111111"],
      );
      const innerEncoded2 = encodeAbiParameters(
        parseAbiParameters("uint256, address"),
        [200n, "0x2222222222222222222222222222222222222222"],
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
              compValue: encodeAbiParameters(parseAbiParameters("bytes[]"), [
                targetArray,
              ]),
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
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        toHex(packConditions(flat)),
        ExecutionOptions.Both,
      ]);

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [targetArray],
          }),
          0,
        ],
        { account: member.account },
      );

      const badInner = encodeAbiParameters(
        parseAbiParameters("uint256, address"),
        [999n, "0x1111111111111111111111111111111111111111"],
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [[badInner, innerEncoded2]],
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

    it("nested tuple - EqualTo on inner tuple", async () => {
      const abi = parseAbi(["function fn(((uint256, uint256), uint256))"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const innerTuple: [bigint, bigint] = [10n, 20n];
      const targetTuple: [[bigint, bigint], bigint] = [innerTuple, 300n];

      await roles.write.allowFunction([
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
                  paramType: Encoding.Tuple,
                  operator: Operator.EqualTo,
                  compValue: encodeAbiParameters(
                    parseAbiParameters("(uint256,uint256)"),
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
      ]);

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [targetTuple],
          }),
          0,
        ],
        { account: member.account },
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [[[99n, 20n], 300n]],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 2n, anyValue],
      );
    });

    it("array of AbiEncoded elements - EqualTo on array", async () => {
      const abi = parseAbi(["function fn(bytes[], uint256)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const innerEncoded1 = encodeAbiParameters(
        parseAbiParameters("uint256, bytes"),
        [50n, "0xaabbccdd"],
      );
      const innerEncoded2 = encodeAbiParameters(
        parseAbiParameters("uint256, bytes"),
        [60n, "0xeeff0011"],
      );
      const targetArray = [innerEncoded1, innerEncoded2];
      const targetDynamic = 777n;

      // Integrity rejects this tree: packed without it, to cover how it is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Array,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("bytes[]"), [
                targetArray,
              ]),
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
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        toHex(packConditions(flat)),
        ExecutionOptions.Both,
      ]);

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [targetArray, targetDynamic],
          }),
          0,
        ],
        { account: member.account },
      );

      const badInner = encodeAbiParameters(
        parseAbiParameters("uint256, bytes"),
        [999n, "0xaabbccdd"],
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [[badInner, innerEncoded2], targetDynamic],
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

  describe("edge cases for complex types", () => {
    it("handles maximum practical nesting depth", async () => {
      const abi = parseAbi([
        "function fn((((uint256, address), (bytes32, uint256)), ((bool, uint8), (int256, address))))",
      ]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetTuple: [
        [[bigint, Address], [Hex, bigint]],
        [[boolean, number], [bigint, Address]],
      ] = [
        [
          [100n, "0x1111111111111111111111111111111111111111"],
          [zeroHash, 200n],
        ],
        [
          [true, 255],
          [-100n, "0x2222222222222222222222222222222222222222"],
        ],
      ];

      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(
                parseAbiParameters(
                  "(((uint256,address),(bytes32,uint256)),((bool,uint8),(int256,address)))",
                ),
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
      ]);

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [targetTuple],
          }),
          0,
        ],
        { account: member.account },
      );
    });

    it.skip("handles large condition trees (600 nodes)", async () => {
      // Limited by block gas (100M in hardhat config)
      // 1 AbiEncoded + 1 Tuple + X*(1 Array + 1 Tuple + 4 Static) = 602
      // 2 + 6X = 602 => X = 100 array fields (602 nodes)

      const innerTupleType = "(uint256, uint256, uint256, address)";
      const arrayCount = 100;
      const fields = Array(arrayCount).fill(`${innerTupleType}[]`);
      const outerTupleType = `(${fields.join(", ")})`;

      const abi: Abi = parseAbi([`function fn(${outerTupleType})`]);
      const { roles, member, testContractAddress, allowTarget } =
        await loadFixture(setupTestContract);

      // Each array has 2 tuples
      const innerTuple: [bigint, bigint, bigint, Address] = [
        42n,
        100n,
        200n,
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
              compValue: encodeAbiParameters(
                parseAbiParameters(outerTupleType),
                [targetValue],
              ),
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

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [targetValue],
          }),
          0,
        ],
        { account: member.account },
      );
    });

    it("handles tuples with many fields (10+ fields)", async () => {
      const abi = parseAbi([
        "function fn((uint256, uint256, uint256, uint256, uint256, uint256, uint256, uint256, uint256, uint256, address))",
      ]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const targetTuple: [
        bigint,
        bigint,
        bigint,
        bigint,
        bigint,
        bigint,
        bigint,
        bigint,
        bigint,
        bigint,
        Address,
      ] = [
        1n,
        2n,
        3n,
        4n,
        5n,
        6n,
        7n,
        8n,
        9n,
        10n,
        "0x1111111111111111111111111111111111111111",
      ];

      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(
                parseAbiParameters(
                  "(uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,uint256,address)",
                ),
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
      ]);

      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [targetTuple],
          }),
          0,
        ],
        { account: member.account },
      );
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
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                100n,
              ]),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(999n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          1n, // EqualTo node at BFS index 1
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
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("uint256"), [
                100n,
              ]),
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(999n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.ParameterNotAllowed,
          anyValue,
          4n, // calldataOffset: parameter starts at byte 4 (after selector)
        ],
      );
    });
  });

  describe.skip("integrity", () => {
    it("reverts UnsuitableParameterType for invalid encodings", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      for (const encoding of [Encoding.None, Encoding.AbiEncoded]) {
        await viem.assertions.revertWithCustomError(
          allowTarget([
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.EqualTo,
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

    it("reverts UnsuitableCompValue when compValue is empty", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      await viem.assertions.revertWithCustomError(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.EqualTo,
            compValue: "0x",
          },
        ]),
        evaluator,
        "UnsuitableCompValue",
      );
    });
  });
});
