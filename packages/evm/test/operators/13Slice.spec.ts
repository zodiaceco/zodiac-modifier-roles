import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { AbiCoder, hexlify, randomBytes, solidityPacked } from "ethers";

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

// compValue layout: 2 bytes shift + 1 byte size
const encodeCompValue = (shift: number, size: number) =>
  solidityPacked(["uint16", "uint8"], [shift, size]);

function replaceBytes(data: string, byteOffset: number, replacement: string) {
  const hex = data.slice(2);
  const replacementHex = replacement.slice(2);
  const start = byteOffset * 2;
  const end = start + replacementHex.length;
  return `0x${hex.slice(0, start)}${replacementHex}${hex.slice(end)}`;
}

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupOneParam = setupFn("function fn(uint256)");
const setupDynamicParam = setupFn("function fn(bytes)");

describe("Operator - Slice", () => {
  after(async () => {
    await connection.close();
  });

  describe("extraction", () => {
    it("extracts 2-byte shift from compValue", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice 4 bytes at shift 4 (skip first 4 bytes)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(4, 4), // shift=4, size=4
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
        ExecutionOptions.Both,
      );

      // bytes: [4 bytes prefix][0xdeadbeef][suffix]
      // Slice extracts bytes 4-7 which should equal 0xdeadbeef
      await expect(invoke("0x00000000deadbeef00000000")).to.not.be.revert(
        ethers,
      );

      // Wrong value at the slice position
      await expect(invoke("0x00000000cafebabe00000000"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);

      // Value at wrong position (shift 0 instead of 4) - fails
      await expect(invoke("0xdeadbeef0000000000000000"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);
    });

    it("extracts 1-byte size from compValue (size 1)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice 1 byte at shift 0
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 1), // shift=0, size=1
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualTo,
                  // Single byte 0xab right-aligned to 32 bytes
                  compValue: abiCoder.encode(["uint256"], [0xab]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // bytes starting with 0xab - passes
      await expect(invoke("0xab00000000000000")).to.not.be.revert(ethers);

      // bytes starting with 0xcd - fails
      await expect(invoke("0xcd00000000000000"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);
    });

    it("extracts 1-byte size from compValue (size 32)", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice 32 bytes at shift 0 (full word)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 32), // shift=0, size=32
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
        ExecutionOptions.Both,
      );

      // 32 bytes encoding 12345 - passes
      await expect(
        invoke(abiCoder.encode(["uint256"], [12345])),
      ).to.not.be.revert(ethers);

      // 32 bytes encoding different value - fails
      await expect(invoke(abiCoder.encode(["uint256"], [12346])))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 2, anyValue);
    });

    it("rejects dynamic slices beyond the declared byte length", async () => {
      const { roles, member, testContractAddress, fn, allowFunction } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(1, 4),
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
        ExecutionOptions.Both,
      );

      const call = replaceBytes(
        ethers.Interface.from(["function fn(bytes)"]).encodeFunctionData(fn, [
          "0x01",
        ]),
        69,
        "0xdeadbeef",
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, call, 0),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.CalldataOverflow, 1, anyValue);
    });
  });

  describe("propagation", () => {
    it("propagates result from child", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice 4 bytes, child checks GreaterThan 100
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4), // shift=0, size=4
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.GreaterThan,
                  compValue: abiCoder.encode(["uint256"], [100]),
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Value 101 > 100 - child passes, Slice propagates success
      await expect(invoke("0x00000065")).to.not.be.revert(ethers); // 101 in 4 bytes

      // Value 100 not > 100 - child fails with ParameterLessThanAllowed, Slice propagates
      await expect(invoke("0x00000064")) // 100 in 4 bytes
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterLessThanAllowed,
          2,
          anyValue,
        );
    });

    it("propagates consumption from child", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      const allowanceKey = hexlify(randomBytes(32));

      // Set up allowance of 100
      await roles.setAllowance(allowanceKey, 100, 0, 0, 0, 0);

      // Slice 32 bytes, child consumes via WithinAllowance
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 32), // shift=0, size=32
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.WithinAllowance,
                  compValue: allowanceKey,
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Consume 30 from sliced value
      await expect(invoke(abiCoder.encode(["uint256"], [30]))).to.not.be.revert(
        ethers,
      );

      // Consumption propagated through Slice - remaining is 70
      const { balance } = await roles.accruedAllowance(allowanceKey);
      expect(balance).to.equal(70);
    });

    it("frames a Bitmask child by the slice window", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice the first 4 bytes, then Bitmask them. The Bitmask operand must be
      // framed by the 4-byte window, not a full 32-byte word.
      // compValue: shift(0x0000) + mask(0xffffffff) + expected(0xdeadbeef)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4), // shift=0, size=4
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Bitmask,
                  compValue: "0x0000ffffffffdeadbeef",
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke("0xdeadbeefcafe")).to.not.be.revert(ethers);
      await expect(invoke("0xcafebabe1234"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.BitmaskNotAllowed,
          anyValue,
          anyValue,
        );
    });

    it("reverts BitmaskOverflow when a Bitmask child's mask exceeds the slice window", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      // Slice window is 4 bytes; the Bitmask mask starts at shift 1 and spans 4
      // bytes (1 + 4 = 5 > 4), so it must overflow rather than read the 5th byte
      // that lies outside the sliced window.
      // compValue: shift(0x0001) + mask(0xffffffff) + expected(0x00000000)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4), // shift=0, size=4
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Bitmask,
                  compValue: "0x0001ffffffff00000000",
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke("0xdeadbeefcafe"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.BitmaskOverflow, anyValue, anyValue);
    });

    it("frames Bitmask under a Slice of a static operand", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Slice,
              compValue: encodeCompValue(28, 4),
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Bitmask,
                  compValue: "0x0000ffffffffdeadbeef",
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke(0xdeadbeef)).to.not.be.revert(ethers);
      await expect(invoke(0xcafebabe))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.BitmaskNotAllowed,
          anyValue,
          anyValue,
        );
    });

    it("propagates the narrowed frame through nested slices", async () => {
      const { roles, roleKey, testContractAddress, fn, invoke } =
        await loadFixture(setupDynamicParam);

      // Integrity rejects a Slice of a Slice: packed without it, to cover how it
      // is read
      const flat = toFlatNodes(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(1, 6),
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Slice,
                  compValue: encodeCompValue(0, 4),
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.Bitmask,
                      compValue: "0x0000ffffffffdeadbeef",
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

      await expect(invoke("0xaadeadbeefbbcc")).to.not.be.revert(ethers);
      await expect(invoke("0xaacafebabebbcc"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.BitmaskNotAllowed,
          anyValue,
          anyValue,
        );
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4), // shift=0, size=4
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
      );

      await expect(invoke("0xcafebabe"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          2, // EqualTo node at BFS index 2
          anyValue,
        );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupDynamicParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4), // shift=0, size=4
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
      );

      await expect(invoke("0xcafebabe"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.ParameterNotAllowed,
          anyValue,
          68, // calldataOffset: bytes data at byte 68 (4 + 32 + 32)
        );
    });
  });

  describe("integrity", () => {
    it("reverts UnsuitableParameterType for invalid encodings", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      for (const encoding of [Encoding.Tuple, Encoding.Array]) {
        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4),
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableParameterType");
      }
    });

    describe("compValue", () => {
      it("reverts UnsuitableCompValue when compValue is not 3 bytes", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Slice,
              compValue: "0x0000", // 2 bytes instead of 3
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
      });

      it("reverts UnsuitableCompValue when size is 0", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 0), // size=0 not allowed
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
      });

      it("reverts UnsuitableCompValue when size is greater than 32", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 33), // size=33 exceeds max
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
      });
    });

    describe("children", () => {
      it("reverts UnsuitableChildCount when Slice has more than one child", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Slice,
              compValue: encodeCompValue(0, 4),
            },
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            },
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableChildCount");
      });

      it("reverts SliceChildNotStatic when Slice child is not Static", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        // All non-Static encodings should be rejected
        for (const encoding of [
          Encoding.None,
          Encoding.Dynamic,
          Encoding.Tuple,
          Encoding.AbiEncoded,
          Encoding.EtherValue,
        ]) {
          await expect(
            allowTarget([
              {
                parent: 0,
                paramType: Encoding.Static,
                operator: Operator.Slice,
                compValue: encodeCompValue(0, 4),
              },
              {
                parent: 0,
                paramType: encoding,
                operator: Operator.Pass,
                compValue: "0x",
              },
            ]),
          ).to.be.revertedWithCustomError(evaluator, "SliceChildNotStatic");
        }
      });
    });
  });
});
