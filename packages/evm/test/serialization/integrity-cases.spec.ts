/**
 * Runs the cases of `specs/integrity.cases.ts` against the contract.
 *
 * A valid case packs. An invalid case reverts with the error of its rule.
 *
 * The cases go through `Evaluator.pack`, not `Roles.packConditions`, which
 * returns before Integrity runs when the array is empty.
 */
import assert from "node:assert/strict";
import { after, before, describe, it } from "node:test";
import { network } from "hardhat";
import { decodeErrorResult } from "viem";

import { integrityCases, type Flat } from "../../specs/integrity.cases.js";
import { createSetup, type EvaluatorContract } from "../setup.js";
import { extractRevertData } from "../utils.js";

const connection = await network.create();
const { deployEvaluator } = createSetup(connection);

describe("Integrity cases", () => {
  let evaluator: EvaluatorContract;

  before(async () => {
    evaluator = await deployEvaluator();
  });

  after(async () => {
    await connection.close();
  });

  /** What the contract does with `flat`: `accepted`, or `Error(args)`. */
  async function outcome(flat: Flat[]): Promise<string> {
    try {
      await evaluator.read.pack([flat]);
      return "accepted";
    } catch (e: unknown) {
      const data = extractRevertData(e);
      if (!data) throw e;
      const { errorName, args } = decodeErrorResult({
        abi: evaluator.abi,
        data,
      });
      return `${errorName}(${(args ?? []).join(", ")})`;
    }
  }

  for (const { rule, name, flat, valid, error } of integrityCases) {
    it(`${rule} ${valid ? "accepts" : "rejects"} ${name}`, async () => {
      const expected = error
        ? `${error.name}(${error.args.join(", ")})`
        : "accepted";
      assert.equal(await outcome(flat), expected);
    });
  }
});
