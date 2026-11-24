/**
 * End to end on the Roles contract: trees checked and packed by the SDK
 * (`checkAndPack`, packages/sdk/src/main/condition/packConditions.ts) are
 * stored with `allowFunctionPacked` and enforced as intended, including
 * shapes `allowFunction` (Integrity) used to reject although they are read
 * correctly (INTEGRITY_BACKLOG.md items 4 and 10). Integrity now accepts
 * them too.
 */
import assert from "node:assert/strict";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import {
  encodeAbiParameters,
  encodeFunctionData,
  parseAbi,
  toFunctionSelector,
  type Abi,
  type AbiFunction,
  type Hex,
} from "viem";

import { checkAndPack } from "../../../sdk/src/main/condition/packConditions.js";
import { createSetup } from "../../test/setup.js";
import {
  Encoding,
  ExecutionOptions,
  Operator,
  flattenCondition,
} from "../../test/utils.js";

const connection = await network.create();
const { viem } = connection;
const { setupTestContract } = createSetup(connection);

const word = (n: number | bigint): Hex =>
  encodeAbiParameters([{ type: "uint256" }], [BigInt(n)]);
const pass = (paramType: Encoding, children?: any[]) => ({
  paramType,
  operator: Operator.Pass,
  children,
});
const eq = (n: number | bigint) => ({
  paramType: Encoding.Static,
  operator: Operator.EqualTo,
  compValue: word(n),
});
const pluck = (paramType: Encoding, slot: number, children?: any[]) => ({
  paramType,
  operator: Operator.Pluck,
  compValue: ("0x" + slot.toString(16).padStart(2, "0")) as Hex,
  children,
});
const zipEvery = (slots: number[], fields: any[]) => ({
  paramType: Encoding.None,
  operator: Operator.ZipEvery,
  compValue: ("0x" +
    slots.map((s) => s.toString(16).padStart(2, "0")).join("")) as Hex,
  children: [
    { paramType: Encoding.Tuple, operator: Operator.Matches, children: fields },
  ],
});

async function setup(signature: string) {
  const env = await setupTestContract();
  const abi = parseAbi([`function ${signature}`] as readonly string[]) as Abi;
  const fn = abi[0] as AbiFunction;
  const selector = toFunctionSelector(fn);
  const invoke = (...args: unknown[]) =>
    env.roles.write.execTransactionFromModule(
      [
        env.testContractAddress,
        0n,
        encodeFunctionData({
          abi: [fn],
          functionName: fn.name,
          args: args as never,
        }),
        0,
      ],
      { account: env.member.account },
    );
  const store = (tree: any) => {
    const { packed } = checkAndPack(flattenCondition(tree) as any);
    return env.roles.write.allowFunctionPacked([
      env.roleKey,
      env.testContractAddress,
      selector,
      packed,
      ExecutionOptions.None,
    ]);
  };
  const storeValidated = (tree: any) =>
    env.roles.write.allowFunction([
      env.roleKey,
      env.testContractAddress,
      selector,
      flattenCondition(tree),
      ExecutionOptions.None,
    ]);
  return { ...env, invoke, store, storeValidated };
}

describe("SDK checkAndPack + allowFunctionPacked on Roles", () => {
  after(async () => {
    await connection.close();
  });

  it("stores the same buffer allowFunction would, and enforces it", async () => {
    const { roles, invoke, store, storeValidated } = await setup(
      "fn(uint256, uint256)",
    );
    const tree = {
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [pass(Encoding.Static), eq(1000)],
    };
    const { packed } = checkAndPack(flattenCondition(tree) as any);
    await viem.assertions.emitWithArgs(
      storeValidated(tree),
      roles,
      "AllowFunction",
      [anyValue, anyValue, anyValue, packed, anyValue],
    );
    await store(tree);
    await invoke(1n, 1000n);
    await viem.assertions.revertWithCustomError(
      invoke(1n, 999n),
      roles,
      "ConditionViolation",
    );
  });

  it("enforces a Zip over plucked arrays", async () => {
    const { roles, invoke, store } = await setup("fn(uint256[], uint256[])");
    const el = () => [pass(Encoding.Static)];
    const tree = {
      paramType: Encoding.None,
      operator: Operator.And,
      children: [
        {
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            pluck(Encoding.Array, 0, el()),
            pluck(Encoding.Array, 1, el()),
          ],
        },
        zipEvery([0, 1], [eq(5), pass(Encoding.Static)]),
      ],
    };
    await store(tree);
    await invoke([5n, 5n], [1n, 2n]);
    await viem.assertions.revertWithCustomError(
      invoke([5n, 6n], [1n, 2n]),
      roles,
      "ConditionViolation",
    );
  });

  it("stores and enforces Slice next to a plain check", async () => {
    const { roles, invoke, store, storeValidated } = await setup("fn(uint256)");
    // last byte == 1 and value < 1000
    const tree = {
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Slice,
              compValue: "0x001f01",
              children: [eq(1)],
            },
            {
              paramType: Encoding.Static,
              operator: Operator.LessThan,
              compValue: word(1000),
            },
          ],
        },
      ],
    };
    await storeValidated(tree);
    await store(tree);
    await invoke(257n);
    await viem.assertions.revertWithCustomError(
      invoke(2n),
      roles,
      "ConditionViolation",
    );
    await viem.assertions.revertWithCustomError(
      invoke(1025n),
      roles,
      "ConditionViolation",
    );
  });

  it("stores and enforces a Zip next to a tuple check", async () => {
    const { roles, invoke, store, storeValidated } = await setup(
      "fn((uint256[], uint256[], string))",
    );
    const el = () => [pass(Encoding.Static)];
    const tree = {
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
              children: [
                pluck(Encoding.Array, 0, el()),
                pluck(Encoding.Array, 1, el()),
                pass(Encoding.Dynamic),
              ],
            },
            zipEvery([0, 1], [pass(Encoding.Static), eq(7)]),
          ],
        },
      ],
    };
    await storeValidated(tree);
    await store(tree);
    await invoke([[1n, 2n], [7n, 7n], "hi"]);
    await viem.assertions.revertWithCustomError(
      invoke([[1n, 2n], [7n, 8n], "hi"]),
      roles,
      "ConditionViolation",
    );
  });

  it("refuses to pack a tree the check rejects (Zip among parameters)", () => {
    const el = () => [pass(Encoding.Static)];
    const bypass = {
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        pluck(Encoding.Array, 0, el()),
        pluck(Encoding.Array, 1, el()),
        zipEvery([0, 1], [eq(5), pass(Encoding.Static)]),
        eq(5),
      ],
    };
    assert.throws(
      () => checkAndPack(flattenCondition(bypass) as any),
      /rejected/,
    );
  });
  it("enforces a parameter after a fixed-size array (described as a tuple, as the SDK does)", async () => {
    const { roles, invoke, store } = await setup("fn(uint256[2], uint256)");
    const tree = {
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        pass(Encoding.Tuple, [pass(Encoding.Static), pass(Encoding.Static)]),
        eq(5),
      ],
    };
    await store(tree);
    await invoke([1n, 2n], 5n);
    await viem.assertions.revertWithCustomError(
      invoke([1n, 2n], 999n),
      roles,
      "ConditionViolation",
    );
    // array elements are values, not offsets
    await viem.assertions.revertWithCustomError(
      invoke([32n, 5n], 999n),
      roles,
      "ConditionViolation",
    );
  });
});
