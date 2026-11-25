/**
 * Integrity at scale: trees larger than any single rule needs, accepted
 * through `Roles.packConditions`.
 *
 * The rules themselves are covered by `integrity-cases.spec.ts`, which runs
 * the cases of `specs/integrity.cases.ts`.
 */
import { after, before, describe, it } from "node:test";
import { network } from "hardhat";
import type { Hex } from "viem";

import { createSetup } from "../setup.js";
import {
  Encoding as E,
  Operator as O,
  type ConditionFlat,
  type RolesContract,
} from "../utils.js";

const connection = await network.create();
const { viem } = connection;
const { deployEvaluator, deployRolesMod } = createSetup(connection);

type N = { paramType: E; operator: O; compValue: Hex; children: N[] };

const node = (paramType: E, operator: O, ...children: N[]): N => ({
  paramType,
  operator,
  compValue: "0x",
  children,
});

/** A word and a `bytes` parameter, unchecked. */
const S = node(E.Static, O.Pass);
const D = node(E.Dynamic, O.Pass);
const call = (...children: N[]) => node(E.AbiEncoded, O.Matches, ...children);
const tuple = (...children: N[]) => node(E.Tuple, O.Matches, ...children);

function flatten(root: N): ConditionFlat[] {
  const flat: ConditionFlat[] = [];
  const queue = [{ n: root, parent: 0 }];
  for (let i = 0; i < queue.length; i++) {
    const { n, parent } = queue[i];
    flat.push({
      parent,
      paramType: n.paramType,
      operator: n.operator,
      compValue: n.compValue,
    });
    for (const child of n.children) queue.push({ n: child, parent: i });
  }
  return flat;
}

describe("Integrity at scale", () => {
  let roles: RolesContract;

  before(async () => {
    const [owner] = await viem.getWalletClients();
    const evaluator = await deployEvaluator();
    roles = await deployRolesMod(
      owner.account.address,
      owner.account.address,
      owner.account.address,
      evaluator.address,
    );
  });

  after(async () => {
    await connection.close();
  });

  const accepts = (name: string, tree: N) =>
    it(`accepts ${name}`, async () => {
      await roles.read.packConditions([flatten(tree)]);
    });

  const nested = (depth: number): N =>
    depth === 0 ? D : tuple(nested(depth - 1));
  const binary = (depth: number): N =>
    depth === 0 ? D : tuple(binary(depth - 1), binary(depth - 1));

  accepts("16 nested tuples", call(nested(16)));
  accepts("a binary tree of 64 nodes", call(binary(5)));
  accepts(
    "a call with 100 parameters",
    call(...Array.from({ length: 100 }, () => S)),
  );
});
