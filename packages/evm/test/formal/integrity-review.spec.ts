/**
 * The examples of packages/evm/formal/INTEGRITY_REVIEW.md: one tree per
 * class that `allowFunction` (Integrity) rejects with
 * `UnsuitableChildTypeTree` and the SDK check (`checkAndPack`) accepts.
 * Each is stored with `allowFunctionPacked` and enforced as intended.
 */
import { expect } from "chai";
import { AbiCoder, Interface } from "ethers";
import { network } from "hardhat";

import { checkAndPack } from "../../../sdk/src/main/condition/packConditions.js";
import { createSetup } from "../setup.js";
import {
  Encoding,
  ExecutionOptions,
  Operator,
  flattenCondition,
} from "../utils.js";

const connection = await network.create();
const { ethers } = connection;
const { setupTestContract } = createSetup(connection);
const abi = AbiCoder.defaultAbiCoder();

const word = (n: number | bigint) => abi.encode(["uint256"], [n]);
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
  const iface = new Interface([`function ${signature}`]);
  const fn = iface.fragments[0] as any;
  const invoke = (...args: any[]) =>
    env.roles
      .connect(env.member)
      .execTransactionFromModule(
        env.testContractAddress,
        0,
        iface.encodeFunctionData(fn, args),
        0,
      );
  const check = async (tree: any) => {
    await expect(
      env.roles.allowFunction(
        env.roleKey,
        env.testContractAddress,
        fn.selector,
        flattenCondition(tree),
        ExecutionOptions.None,
      ),
    ).to.be.revertedWithCustomError(env.roles, "UnsuitableChildTypeTree");
    const { packed } = checkAndPack(flattenCondition(tree) as any);
    await env.roles.allowFunctionPacked(
      env.roleKey,
      env.testContractAddress,
      fn.selector,
      packed,
      ExecutionOptions.None,
    );
  };
  const ok = async (...args: any[]) =>
    expect(invoke(...args)).to.not.be.revert(ethers);
  const denied = async (...args: any[]) =>
    expect(invoke(...args)).to.be.revertedWithCustomError(
      env.roles,
      "ConditionViolation",
    );
  return { check, ok, denied };
}

describe("Integrity review: trees Integrity rejects, enforced as intended", () => {
  it("1. checks of a prefix of one tuple, side by side", async () => {
    const { check, ok, denied } = await setup("fn((bytes, uint256, uint256))");
    // x.b == 1 || x.c == 2, as normalize leaves it (trailing Pass pruned)
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
    const erc20 = new Interface(["function transfer(address, uint256)"]);
    const [a, b] = [
      "0x000000000000000000000000000000000000aaaa",
      "0x000000000000000000000000000000000000bbbb",
    ];
    const required = erc20.encodeFunctionData("transfer", [a, 5]);
    // every element is transfer(_, amount < 100), and one element is exactly
    // `required`
    await check(
      calldata([
        and([
          node(Encoding.Array, Operator.ArrayEvery, [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              compValue:
                "0x0004" + erc20.getFunction("transfer")!.selector.slice(2),
              children: [pass(Encoding.Static), cmp(Operator.LessThan, 100)],
            },
          ]),
          node(Encoding.Array, Operator.ArraySome, [
            {
              paramType: Encoding.Dynamic,
              operator: Operator.EqualTo,
              compValue: abi.encode(["bytes"], [required]),
            },
          ]),
        ]),
      ]),
    );
    const other = (n: number) => erc20.encodeFunctionData("transfer", [b, n]);
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
