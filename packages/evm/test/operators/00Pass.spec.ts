import { expect } from "chai";
import { network } from "hardhat";

import { createSetup } from "../setup.js";
import {
  Operator,
  Encoding,
  ExecutionOptions,
  flattenCondition,
  packConditions,
} from "../utils.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupOneParam = setupFn("function fn(uint256)");

describe("Operator - Pass", () => {
  after(async () => {
    await connection.close();
  });

  describe("core behavior", () => {
    it("allows any parameter value", async () => {
      const { allowFunction, invoke } = await loadFixture(setupOneParam);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Pass,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Any value passes - the operator performs no validation
      await expect(invoke(0)).to.not.be.revert(ethers);
      await expect(invoke(999)).to.not.be.revert(ethers);
    });
  });

  describe("integrity", () => {
    it("reverts UnsuitableCompValue when compValue is not empty", async () => {
      const { roles, evaluator } = await loadFixture(setupTestContract);

      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x".padEnd(66, "0"),
          },
        ]),
      ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
    });
  });
});
