import { expect } from "chai";
import { AbiCoder, Interface, hexlify, solidityPacked } from "ethers";
import { network } from "hardhat";

import { toFlatNodes } from "../../../sdk/src/main/condition/checkStored.js";
import { packConditions as sdkPackConditions } from "../../../sdk/src/main/condition/packConditions.js";
import { createSetup } from "../setup.js";
import {
  ConditionViolationStatus,
  Encoding,
  ExecutionOptions,
  Operator,
  flattenCondition,
  packConditions,
} from "../utils.js";

const abiCoder = AbiCoder.defaultAbiCoder();

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract } = createSetup(connection);

type ConditionInput = Parameters<typeof flattenCondition>[0];

interface MatrixCase {
  name: string;
  sig: string;
  condition: ConditionInput;
  valid: unknown[];
  invalid: unknown[];
  violatedIndex?: number;
  rawPack?: boolean;
}

const enc = (types: string[], values: unknown[]) =>
  abiCoder.encode(types, values);

const pass = (
  paramType: Encoding,
  children?: ConditionInput[],
): ConditionInput =>
  children
    ? { paramType, operator: Operator.Pass, children }
    : { paramType, operator: Operator.Pass };

const matches = (children: ConditionInput[]): ConditionInput => ({
  paramType: Encoding.AbiEncoded,
  operator: Operator.Matches,
  children,
});

const eq = (
  paramType: Encoding,
  compValue: string,
  children?: ConditionInput[],
): ConditionInput => ({
  paramType,
  operator: Operator.EqualTo,
  compValue,
  ...(children ? { children } : {}),
});

async function runCase(c: MatrixCase) {
  const iface = new Interface([c.sig]);
  const fn = iface.getFunction("fn")!;
  const { roles, member, testContractAddress, roleKey } =
    await loadFixture(setupTestContract);

  const flat = flattenCondition(c.condition);
  const packed = c.rawPack
    ? hexlify(sdkPackConditions(toFlatNodes(flat as any)))
    : await packConditions(roles, flat);

  await roles.allowFunctionPacked(
    roleKey,
    testContractAddress,
    fn.selector,
    packed,
    ExecutionOptions.Both,
  );

  const exec = (args: unknown[]) =>
    roles
      .connect(member)
      .execTransactionFromModule(
        testContractAddress,
        0,
        iface.encodeFunctionData(fn, args),
        0,
      );

  await expect(exec(c.valid)).to.not.be.revert(ethers);
  await expect(exec(c.invalid))
    .to.be.revertedWithCustomError(roles, "ConditionViolation")
    .withArgs(
      ConditionViolationStatus.ParameterNotAllowed,
      c.violatedIndex ?? 1,
      (offset: bigint) => offset >= 4n,
    );
}

describe("AbiLocation", () => {
  after(async () => {
    await connection.close();
  });

  // ───────────────────────────────────────────────────────────────
  // Encoding matrix: every parent → child combination through
  // navigation (`children`/`elements`) and `sliceEncoded` (`EqualTo`)
  // ───────────────────────────────────────────────────────────────
  describe("Parent: Tuple", () => {
    const cases: MatrixCase[] = [
      {
        name: "T→S inline: f((uint256))",
        sig: "function fn((uint256))",
        condition: matches([
          eq(Encoding.Tuple, enc(["(uint256)"], [[42]]), [
            pass(Encoding.Static),
          ]),
        ]),
        valid: [[42]],
        invalid: [[999]],
      },
      {
        name: "T→D pointer: f((uint256, bytes))",
        sig: "function fn((uint256, bytes))",
        condition: matches([
          eq(Encoding.Tuple, enc(["(uint256,bytes)"], [[42, "0xdeadbeef"]]), [
            pass(Encoding.Static),
            pass(Encoding.Dynamic),
          ]),
        ]),
        valid: [[42, "0xdeadbeef"]],
        invalid: [[42, "0xaa"]],
      },
      {
        name: "T→T inline: f(((uint256, uint256), uint256))",
        sig: "function fn(((uint256, uint256), uint256))",
        condition: matches([
          eq(
            Encoding.Tuple,
            enc(["((uint256,uint256),uint256)"], [[[10, 20], 30]]),
            [
              pass(Encoding.Tuple, [
                pass(Encoding.Static),
                pass(Encoding.Static),
              ]),
              pass(Encoding.Static),
            ],
          ),
        ]),
        valid: [[[10, 20], 30]],
        invalid: [[[99, 20], 30]],
      },
      {
        name: "T→T pointer: f((uint256, (uint256, bytes)))",
        sig: "function fn((uint256, (uint256, bytes)))",
        condition: matches([
          eq(
            Encoding.Tuple,
            enc(["(uint256,(uint256,bytes))"], [[42, [100, "0xaabb"]]]),
            [
              pass(Encoding.Static),
              pass(Encoding.Tuple, [
                pass(Encoding.Static),
                pass(Encoding.Dynamic),
              ]),
            ],
          ),
        ]),
        valid: [[42, [100, "0xaabb"]]],
        invalid: [[42, [999, "0xaabb"]]],
      },
      {
        name: "T→A pointer: f((uint256[]))",
        sig: "function fn((uint256[]))",
        condition: matches([
          eq(Encoding.Tuple, enc(["(uint256[])"], [[[1, 2, 3]]]), [
            pass(Encoding.Array, [pass(Encoding.Static)]),
          ]),
        ]),
        valid: [[[1, 2, 3]]],
        invalid: [[[1, 2, 99]]],
      },
      {
        name: "T→E pointer: f((uint256, bytes)) with AbiEncoded child",
        sig: "function fn((uint256, bytes))",
        condition: matches([
          eq(
            Encoding.Tuple,
            enc(["(uint256,bytes)"], [[42, enc(["uint256"], [777])]]),
            [
              pass(Encoding.Static),
              pass(Encoding.AbiEncoded, [pass(Encoding.Static)]),
            ],
          ),
        ]),
        valid: [[42, enc(["uint256"], [777])]],
        invalid: [[42, enc(["uint256"], [999])]],
      },
      {
        name: "T→N inline: f((uint256, uint256)) with None-wrapped child",
        sig: "function fn((uint256, uint256))",
        condition: matches([
          eq(Encoding.Tuple, enc(["(uint256,uint256)"], [[10, 20]]), [
            pass(Encoding.Static),
            pass(Encoding.None, [pass(Encoding.Static)]),
          ]),
        ]),
        valid: [[10, 20]],
        invalid: [[10, 99]],
        rawPack: true,
      },
      {
        name: "T→N pointer: f((uint256, bytes)) with None-wrapped dynamic child",
        sig: "function fn((uint256, bytes))",
        condition: matches([
          eq(Encoding.Tuple, enc(["(uint256,bytes)"], [[42, "0xaabbccdd"]]), [
            pass(Encoding.Static),
            pass(Encoding.None, [pass(Encoding.Dynamic)]),
          ]),
        ]),
        valid: [[42, "0xaabbccdd"]],
        invalid: [[42, "0xff"]],
        rawPack: true,
      },
    ];

    for (const c of cases) {
      it(c.name, () => runCase(c));
    }
  });

  describe("Parent: Array", () => {
    const cases: MatrixCase[] = [
      {
        name: "A→S inline: f(uint256[])",
        sig: "function fn(uint256[])",
        condition: matches([
          eq(Encoding.Array, enc(["uint256[]"], [[10, 20, 30]]), [
            pass(Encoding.Static),
          ]),
        ]),
        valid: [[10, 20, 30]],
        invalid: [[10, 20, 99]],
      },
      {
        name: "A→S empty: f(uint256[])",
        sig: "function fn(uint256[])",
        condition: matches([
          eq(Encoding.Array, enc(["uint256[]"], [[]]), [pass(Encoding.Static)]),
        ]),
        valid: [[]],
        invalid: [[1]],
      },
      {
        name: "A→D pointer: f(bytes[])",
        sig: "function fn(bytes[])",
        condition: matches([
          eq(Encoding.Array, enc(["bytes[]"], [["0xaabb", "0xccddee"]]), [
            pass(Encoding.Dynamic),
          ]),
        ]),
        valid: [["0xaabb", "0xccddee"]],
        invalid: [["0xaabb", "0xff"]],
      },
      {
        name: "A→D empty: f(bytes[])",
        sig: "function fn(bytes[])",
        condition: matches([
          eq(Encoding.Array, enc(["bytes[]"], [[]]), [pass(Encoding.Dynamic)]),
        ]),
        valid: [[]],
        invalid: [["0xaa"]],
      },
      {
        name: "A→T inline: f((uint256, uint256)[])",
        sig: "function fn((uint256, uint256)[])",
        condition: matches([
          eq(
            Encoding.Array,
            enc(
              ["(uint256,uint256)[]"],
              [
                [
                  [1, 2],
                  [3, 4],
                ],
              ],
            ),
            [
              pass(Encoding.Tuple, [
                pass(Encoding.Static),
                pass(Encoding.Static),
              ]),
            ],
          ),
        ]),
        valid: [
          [
            [1, 2],
            [3, 4],
          ],
        ],
        invalid: [
          [
            [1, 99],
            [3, 4],
          ],
        ],
      },
      {
        name: "A→T pointer: f((uint256, bytes)[])",
        sig: "function fn((uint256, bytes)[])",
        condition: matches([
          eq(
            Encoding.Array,
            enc(
              ["(uint256,bytes)[]"],
              [
                [
                  [1, "0xaa"],
                  [2, "0xbb"],
                ],
              ],
            ),
            [
              pass(Encoding.Tuple, [
                pass(Encoding.Static),
                pass(Encoding.Dynamic),
              ]),
            ],
          ),
        ]),
        valid: [
          [
            [1, "0xaa"],
            [2, "0xbb"],
          ],
        ],
        invalid: [
          [
            [1, "0xaa"],
            [2, "0xff"],
          ],
        ],
      },
      {
        name: "A→A pointer: f(uint256[][])",
        sig: "function fn(uint256[][])",
        condition: matches([
          eq(
            Encoding.Array,
            enc(
              ["uint256[][]"],
              [
                [
                  [1, 2],
                  [3, 4, 5],
                ],
              ],
            ),
            [pass(Encoding.Array, [pass(Encoding.Static)])],
          ),
        ]),
        valid: [
          [
            [1, 2],
            [3, 4, 5],
          ],
        ],
        invalid: [
          [
            [1, 2],
            [3, 4, 99],
          ],
        ],
      },
      {
        name: "A→E pointer: f(bytes[]) with AbiEncoded elements",
        sig: "function fn(bytes[])",
        condition: matches([
          eq(
            Encoding.Array,
            enc(
              ["bytes[]"],
              [[enc(["uint256"], [100]), enc(["uint256"], [200])]],
            ),
            [pass(Encoding.AbiEncoded, [pass(Encoding.Static)])],
          ),
        ]),
        valid: [[enc(["uint256"], [100]), enc(["uint256"], [200])]],
        invalid: [[enc(["uint256"], [999]), enc(["uint256"], [200])]],
      },
      {
        name: "A→N inline: f(uint256[]) with None-wrapped element",
        sig: "function fn(uint256[])",
        condition: matches([
          eq(Encoding.Array, enc(["uint256[]"], [[10, 20, 30]]), [
            pass(Encoding.None, [pass(Encoding.Static)]),
          ]),
        ]),
        valid: [[10, 20, 30]],
        invalid: [[10, 20, 99]],
        rawPack: true,
      },
      {
        name: "A→N pointer: f(bytes[]) with None-wrapped dynamic element",
        sig: "function fn(bytes[])",
        condition: matches([
          eq(Encoding.Array, enc(["bytes[]"], [["0xaabb", "0xccdd"]]), [
            pass(Encoding.None, [pass(Encoding.Dynamic)]),
          ]),
        ]),
        valid: [["0xaabb", "0xccdd"]],
        invalid: [["0xaabb", "0xff"]],
        rawPack: true,
      },
    ];

    for (const c of cases) {
      it(c.name, () => runCase(c));
    }
  });

  describe("Parent: AbiEncoded", () => {
    const cases: MatrixCase[] = [
      {
        name: "E→S inline: f(uint256)",
        sig: "function fn(uint256)",
        condition: matches([eq(Encoding.Static, enc(["uint256"], [12345]))]),
        valid: [12345],
        invalid: [99999],
      },
      {
        name: "E→D pointer: f(bytes)",
        sig: "function fn(bytes)",
        condition: matches([
          eq(Encoding.Dynamic, enc(["bytes"], ["0xdeadbeef"])),
        ]),
        valid: ["0xdeadbeef"],
        invalid: ["0xaa"],
      },
      {
        name: "E→T inline: f((uint256, uint256))",
        sig: "function fn((uint256, uint256))",
        condition: matches([
          eq(Encoding.Tuple, enc(["(uint256,uint256)"], [[100, 200]]), [
            pass(Encoding.Static),
            pass(Encoding.Static),
          ]),
        ]),
        valid: [[100, 200]],
        invalid: [[100, 999]],
      },
      {
        name: "E→T pointer: f((uint256, bytes))",
        sig: "function fn((uint256, bytes))",
        condition: matches([
          eq(Encoding.Tuple, enc(["(uint256,bytes)"], [[50, "0xaabb"]]), [
            pass(Encoding.Static),
            pass(Encoding.Dynamic),
          ]),
        ]),
        valid: [[50, "0xaabb"]],
        invalid: [[50, "0xff"]],
      },
      {
        name: "E→A pointer: f(uint256[])",
        sig: "function fn(uint256[])",
        condition: matches([
          eq(Encoding.Array, enc(["uint256[]"], [[5, 10, 15]]), [
            pass(Encoding.Static),
          ]),
        ]),
        valid: [[5, 10, 15]],
        invalid: [[5, 10, 99]],
      },
      {
        name: "E→E pointer: f(bytes) with nested AbiEncoded Matches",
        sig: "function fn(bytes)",
        condition: matches([
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            compValue: "0x0000",
            children: [
              eq(Encoding.Static, enc(["uint256"], [100])),
              pass(Encoding.Static),
            ],
          },
        ]),
        valid: [enc(["uint256", "uint256"], [100, 200])],
        invalid: [enc(["uint256", "uint256"], [999, 200])],
        violatedIndex: 2,
      },
      {
        name: "E→N inline: f(uint256) with And wrapper",
        sig: "function fn(uint256)",
        condition: matches([
          {
            paramType: Encoding.None,
            operator: Operator.And,
            children: [eq(Encoding.Static, enc(["uint256"], [42]))],
          },
        ]),
        valid: [42],
        invalid: [99],
        violatedIndex: 2,
      },
      {
        name: "E→N pointer: f(bytes) with And wrapper",
        sig: "function fn(bytes)",
        condition: matches([
          {
            paramType: Encoding.None,
            operator: Operator.And,
            children: [eq(Encoding.Dynamic, enc(["bytes"], ["0xaabb"]))],
          },
        ]),
        valid: ["0xaabb"],
        invalid: ["0xff"],
        violatedIndex: 2,
      },
    ];

    for (const c of cases) {
      it(c.name, () => runCase(c));
    }
  });

  describe("Parent: None", () => {
    const and = (children: ConditionInput[]): ConditionInput => ({
      paramType: Encoding.None,
      operator: Operator.And,
      children,
    });

    const cases: MatrixCase[] = [
      {
        name: "N→S inline: f(uint256)",
        sig: "function fn(uint256)",
        condition: and([
          matches([eq(Encoding.Static, enc(["uint256"], [42]))]),
        ]),
        valid: [42],
        invalid: [99],
        violatedIndex: 2,
      },
      {
        name: "N→D pointer: f(bytes)",
        sig: "function fn(bytes)",
        condition: and([
          matches([eq(Encoding.Dynamic, enc(["bytes"], ["0xaabb"]))]),
        ]),
        valid: ["0xaabb"],
        invalid: ["0xff"],
        violatedIndex: 2,
      },
      {
        name: "N→T inline: f((uint256, uint256))",
        sig: "function fn((uint256, uint256))",
        condition: and([
          matches([
            eq(Encoding.Tuple, enc(["(uint256,uint256)"], [[10, 20]]), [
              pass(Encoding.Static),
              pass(Encoding.Static),
            ]),
          ]),
        ]),
        valid: [[10, 20]],
        invalid: [[10, 99]],
        violatedIndex: 2,
      },
      {
        name: "N→A pointer: f(uint256[])",
        sig: "function fn(uint256[])",
        condition: and([
          matches([
            eq(Encoding.Array, enc(["uint256[]"], [[5, 10, 15]]), [
              pass(Encoding.Static),
            ]),
          ]),
        ]),
        valid: [[5, 10, 15]],
        invalid: [[5, 10, 99]],
        violatedIndex: 2,
      },
      {
        name: "N→E pointer: f(bytes) with nested AbiEncoded Matches",
        sig: "function fn(bytes)",
        condition: and([
          matches([
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0000",
              children: [eq(Encoding.Static, enc(["uint256"], [42]))],
            },
          ]),
        ]),
        valid: [enc(["uint256"], [42])],
        invalid: [enc(["uint256"], [999])],
        violatedIndex: 3,
      },
      {
        name: "N→N: f(uint256) with double And wrapper",
        sig: "function fn(uint256)",
        condition: and([
          and([matches([eq(Encoding.Static, enc(["uint256"], [42]))])]),
        ]),
        valid: [42],
        invalid: [99],
        violatedIndex: 3,
      },
    ];

    for (const c of cases) {
      it(c.name, () => runCase(c));
    }
  });

  // ───────────────────────────────────────────────────────────────
  // Exact `calldataOffset` reported in ConditionViolation (`offsetOf`)
  // ───────────────────────────────────────────────────────────────
  describe("Violation calldataOffset", () => {
    it("static second param: 4 (selector) + 32 (param0) = 36", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);
      const iface = new Interface(["function fn(uint256, uint256)"]);
      const fn = iface.getFunction("fn")!;

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition(
          matches([
            pass(Encoding.Static),
            eq(Encoding.Static, enc(["uint256"], [1])),
          ]),
        ),
        ExecutionOptions.None,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [0, 2]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, 36);
    });

    it("dynamic tail: 4 (selector) + 32 (head offset) = 36", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);
      const iface = new Interface(["function fn(bytes)"]);
      const fn = iface.getFunction("fn")!;

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition(
          matches([eq(Encoding.Dynamic, enc(["bytes"], ["0x11"]))]),
        ),
        ExecutionOptions.None,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, ["0x22"]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 1, 36);
    });

    it("nested AbiEncoded: 4 (selector) + 32 (ptr) + 32 (bytes len) + 4 (inner selector) + 32 (inner param0) = 104", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);
      const iface = new Interface(["function fn(bytes)"]);
      const fn = iface.getFunction("fn")!;

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition(
          matches([
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004",
              children: [
                pass(Encoding.Static),
                eq(Encoding.Static, enc(["uint256"], [1])),
              ],
            },
          ]),
        ),
        ExecutionOptions.None,
      );

      const inner = "0x11223344" + enc(["uint256", "uint256"], [0, 2]).slice(2);
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [inner]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 3, 104);
    });

    it("Slice on Dynamic (shift = 5): 4 (selector) + 32 (ptr) + 32 (len) + 5 (shift) = 73", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);
      const iface = new Interface(["function fn(bytes)"]);
      const fn = iface.getFunction("fn")!;

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition(
          matches([
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: solidityPacked(["uint16", "uint8"], [5, 4]),
              children: [eq(Encoding.Static, enc(["uint256"], [1]))],
            },
          ]),
        ),
        ExecutionOptions.None,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, ["0x" + "00".repeat(10)]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, 73);
    });

    it("ZipEvery failing on element 1 of the second array: 4 (selector) + 64 (2 head ptrs) + 96 (arr0) + 32 (arr1 count) + 32 (arr1[0]) = 228", async () => {
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);
      const iface = new Interface(["function fn(uint256[], uint256[])"]);
      const fn = iface.getFunction("fn")!;

      await roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            matches([
              {
                paramType: Encoding.Array,
                operator: Operator.Pluck,
                compValue: "0x00",
                children: [pass(Encoding.Static)],
              },
              {
                paramType: Encoding.Array,
                operator: Operator.Pluck,
                compValue: "0x01",
                children: [pass(Encoding.Static)],
              },
            ]),
            {
              paramType: Encoding.None,
              operator: Operator.ZipEvery,
              compValue: "0x0001",
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Matches,
                  children: [
                    eq(Encoding.Static, enc(["uint256"], [1])),
                    eq(Encoding.Static, enc(["uint256"], [2])),
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.None,
      );

      await expect(
        roles.connect(member).execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData(fn, [
            [1, 1],
            [2, 99],
          ]),
          0,
        ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.NotEveryZippedElementPasses, 9, 228);
    });
  });
});
