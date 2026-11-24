/**
 * One tree per class that `allowFunction` (Integrity) used to reject with
 * `UnsuitableChildTypeTree` while the SDK check (`checkAndPack`) accepted
 * it. Integrity now follows the same rules: each is stored with
 * `allowFunction`, packs to the buffer the SDK produces, and is enforced as
 * intended.
 */
import assert from "node:assert/strict";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import {
  encodeAbiParameters,
  encodeFunctionData,
  parseAbi,
  parseAbiParameters,
  toFunctionSelector,
  type Abi,
  type AbiFunction,
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

const word = (n: number | bigint) =>
  encodeAbiParameters(parseAbiParameters("uint256"), [BigInt(n)]);
const pass = (paramType: Encoding, children?: any[]) => ({
  paramType,
  operator: Operator.Pass,
  children,
});
const cmp = (operator: Operator, n: number) => ({
  paramType: Encoding.Static,
  operator,
  compValue: word(n),
});
const node = (paramType: Encoding, operator: Operator, children: any[]) => ({
  paramType,
  operator,
  children,
});
const calldata = (children: any[]) =>
  node(Encoding.AbiEncoded, Operator.Matches, children);
const and = (children: any[]) => node(Encoding.None, Operator.And, children);
const or = (children: any[]) => node(Encoding.None, Operator.Or, children);
const pluck = (slot: number) => ({
  paramType: Encoding.Array,
  operator: Operator.Pluck,
  compValue: "0x" + slot.toString(16).padStart(2, "0"),
  children: [pass(Encoding.Static)],
});

async function setup(signature: string) {
  const env = await setupTestContract();
  const fullSignature: string = `function ${signature}`;
  const abi = parseAbi([fullSignature]) as Abi;
  const fn = abi[0] as AbiFunction;
  const selector = toFunctionSelector(fn);
  const invoke = (...args: any[]) =>
    env.roles.write.execTransactionFromModule(
      [
        env.testContractAddress,
        0n,
        encodeFunctionData({
          abi: [fn],
          functionName: fn.name,
          args,
        }),
        0,
      ],
      { account: env.member.account },
    );
  const check = async (tree: any) => {
    const flat = flattenCondition(tree);
    const { packed } = checkAndPack(flat as any);
    assert.equal(await env.roles.read.packConditions([flat]), packed);
    await env.roles.write.allowFunction([
      env.roleKey,
      env.testContractAddress,
      selector,
      flat,
      ExecutionOptions.None,
    ]);
  };
  const ok = async (...args: any[]) => {
    await invoke(...args);
  };
  const denied = async (...args: any[]) =>
    viem.assertions.revertWithCustomError(
      invoke(...args),
      env.roles,
      "ConditionViolation",
    );
  return { check, ok, denied };
}

describe("Integrity review: trees Integrity used to reject, enforced as intended", () => {
  after(async () => {
    await connection.close();
  });
  it("1. checks of a prefix of one tuple, side by side", async () => {
    const { check, ok, denied } = await setup("fn((bytes, uint256, uint256))");
    // x.b == 1 || x.c == 2, each branch listing only the fields it checks
    await check(
      calldata([
        or([
          node(Encoding.Tuple, Operator.Matches, [
            pass(Encoding.Dynamic),
            cmp(Operator.EqualTo, 1),
          ]),
          node(Encoding.Tuple, Operator.Matches, [
            pass(Encoding.Dynamic),
            pass(Encoding.Static),
            cmp(Operator.EqualTo, 2),
          ]),
        ]),
      ]),
    );
    await ok(["0x1234", 1, 0]);
    await ok(["0x1234", 0, 2]);
    await denied(["0x1234", 0, 0]);
  });

  it("2. a Slice and a plain check of the same type", async () => {
    const { check, ok, denied } = await setup("fn(uint256[])");
    // every element ends in byte 0x01, and some element is > 1000
    const lastByteIs1 = {
      paramType: Encoding.Static,
      operator: Operator.Slice,
      compValue: "0x001f01",
      children: [cmp(Operator.EqualTo, 1)],
    };
    await check(
      calldata([
        and([
          node(Encoding.Array, Operator.ArrayEvery, [lastByteIs1]),
          node(Encoding.Array, Operator.ArraySome, [
            cmp(Operator.GreaterThan, 1000),
          ]),
        ]),
      ]),
    );
    await ok([257, 1025]);
    await denied([257, 513]);
    await denied([1025, 2]);
  });

  it("3. bytes read as nested calldata by one check and as bytes by another", async () => {
    const { check, ok, denied } = await setup("fn(bytes[])");
    const erc20 = parseAbi(["function transfer(address, uint256)"]);
    const [a, b] = [
      "0x000000000000000000000000000000000000aaaa",
      "0x000000000000000000000000000000000000bbbb",
    ] as const;
    const required = encodeFunctionData({
      abi: erc20,
      functionName: "transfer",
      args: [a, 5n],
    });
    // every element is transfer(_, amount < 100), and one element is exactly
    // `required`
    await check(
      calldata([
        and([
          node(Encoding.Array, Operator.ArrayEvery, [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue: "0x0004" + toFunctionSelector(erc20[0]).slice(2),
              children: [pass(Encoding.Static), cmp(Operator.LessThan, 100)],
            },
          ]),
          node(Encoding.Array, Operator.ArraySome, [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: encodeAbiParameters(parseAbiParameters("bytes"), [
                required,
              ]),
            },
          ]),
        ]),
      ]),
    );
    const other = (n: number) =>
      encodeFunctionData({
        abi: erc20,
        functionName: "transfer",
        args: [b, BigInt(n)],
      });
    await ok([required, other(50)]);
    await denied([other(50)]);
    await denied([required, other(500)]);
  });

  it("4. a Zip next to a tuple check", async () => {
    const { check, ok, denied } = await setup(
      "fn((uint256[], uint256[], string))",
    );
    // x.b[i] == 7 for every i, zipped with x.a
    await check(
      calldata([
        and([
          node(Encoding.Tuple, Operator.Matches, [
            pluck(0),
            pluck(1),
            pass(Encoding.Dynamic),
          ]),
          {
            paramType: Encoding.None,
            operator: Operator.ZipEvery,
            compValue: "0x0001",
            children: [
              node(Encoding.Tuple, Operator.Matches, [
                pass(Encoding.Static),
                cmp(Operator.EqualTo, 7),
              ]),
            ],
          },
        ]),
      ]),
    );
    await ok([[1, 2], [7, 7], "hi"]);
    await denied([[1, 2], [7, 8], "hi"]);
  });
});
