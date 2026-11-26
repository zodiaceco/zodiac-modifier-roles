import { after, describe, it } from "node:test";
import { network } from "hardhat";

import { createSetup } from "../setup.js";
import {
  Operator,
  Encoding,
  ExecutionOptions,
  flattenCondition,
} from "../utils.js";

const connection = await network.create();
const { networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupFn } = createSetup(connection);
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
      await invoke(0);
      await invoke(999);
    });
  });
});
