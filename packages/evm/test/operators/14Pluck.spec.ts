import { expect } from "chai";
import { network } from "hardhat";

import { createSetup } from "../setup.js";
import { Encoding, Operator } from "../utils.js";

const connection = await network.create();
const { networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract } = createSetup(connection);

describe("Operator - Pluck", () => {
  after(async () => {
    await connection.close();
  });

  describe("integrity", () => {
    it("reverts UnsuitableParameterType for invalid encodings", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      // Note: Array is now allowed for Pluck (used by Zip operators)

      for (const encoding of [
        Encoding.None,
        Encoding.Dynamic,
        Encoding.Tuple,
        Encoding.AbiEncoded,
      ]) {
        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.Pluck,
              compValue: "0x00",
            },
          ]),
        )
          .to.be.revertedWithCustomError(evaluator, "UnsuitableParameterType")
          .withArgs(0);
      }
    });

    describe("compValue", () => {
      it("reverts UnsuitableCompValue when compValue is not 1 byte", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Pluck,
              compValue: "0x0000", // 2 bytes instead of 1
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
      });

      it("reverts UnsuitableCompValue when index is 255 (reserved)", async () => {
        const { evaluator, allowTarget } = await loadFixture(setupTestContract);

        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Pluck,
              compValue: "0xff", // index 255 is reserved
            },
          ]),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
      });
    });

    it("reverts LeafNodeCannotHaveChildren when Pluck has children", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      await expect(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.Pluck,
            compValue: "0x00",
          },
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithCustomError(evaluator, "LeafNodeCannotHaveChildren");
    });

    it("reverts UnsuitableChildCount when Pluck(Array) has a non-structural child", async () => {
      const { evaluator, allowTarget } = await loadFixture(setupTestContract);

      // The evaluator reads children[0] as the array element template, so a
      // child that reads no calldata must be rejected.
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
            paramType: Encoding.Array,
            operator: Operator.Pluck,
            compValue: "0x00",
          },
          {
            parent: 1,
            paramType: Encoding.None,
            operator: Operator.Pass,
            compValue: "0x",
          },
          {
            parent: 1,
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      )
        .to.be.revertedWithCustomError(evaluator, "UnsuitableChildCount")
        .withArgs(1);
    });
  });
});
