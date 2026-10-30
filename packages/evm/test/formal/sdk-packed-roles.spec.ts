/**
 * End to end on the Roles contract: trees checked and packed by the SDK
 * (`checkAndPack`, packages/sdk/src/main/condition/packConditions.ts) are
 * stored with `allowFunctionPacked` and enforced as intended, including
 * shapes `allowFunction` (Integrity) rejects although they are read correctly
 * (INTEGRITY_BACKLOG.md items 4 and 10).
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
const { ethers, networkHelpers } = connection;
const { setupTestContract } = createSetup(connection);
const abi = AbiCoder.defaultAbiCoder();

const word = (n: number | bigint) => abi.encode(["uint256"], [n]);
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
  compValue: "0x" + slot.toString(16).padStart(2, "0"),
  children,
});
const zipEvery = (slots: number[], fields: any[]) => ({
  paramType: Encoding.None,
  operator: Operator.ZipEvery,
  compValue: "0x" + slots.map((s) => s.toString(16).padStart(2, "0")).join(""),
  children: [
    { paramType: Encoding.Tuple, operator: Operator.Matches, children: fields },
  ],
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
  const store = (tree: any) => {
    const { packed } = checkAndPack(flattenCondition(tree) as any);
    return env.roles.allowFunctionPacked(
      env.roleKey,
      env.testContractAddress,
      fn.selector,
      packed,
      ExecutionOptions.None,
    );
  };
  const storeValidated = (tree: any) =>
    env.roles.allowFunction(
      env.roleKey,
      env.testContractAddress,
      fn.selector,
      flattenCondition(tree),
      ExecutionOptions.None,
    );
  return { ...env, invoke, store, storeValidated };
}

const violation = (roles: any) => [roles, "ConditionViolation"] as const;

describe("SDK checkAndPack + allowFunctionPacked on Roles", () => {
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
    await expect(storeValidated(tree))
      .to.emit(roles, "AllowFunction")
      .withArgs(
        (x: any) => true,
        (x: any) => true,
        (x: any) => true,
        packed,
        (x: any) => true,
      );
    await store(tree);
    await expect(invoke(1, 1000)).to.not.be.revert(ethers);
    await expect(invoke(1, 999)).to.be.revertedWithCustomError(
      ...violation(roles),
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
    await expect(invoke([5, 5], [1, 2])).to.not.be.revert(ethers);
    await expect(invoke([5, 6], [1, 2])).to.be.revertedWithCustomError(
      ...violation(roles),
    );
  });

  it("stores and enforces Slice next to a plain check (Integrity rejects it)", async () => {
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
    await expect(storeValidated(tree)).to.be.revertedWithCustomError(
      roles,
      "UnsuitableChildTypeTree",
    );
    await store(tree);
    await expect(invoke(257)).to.not.be.revert(ethers);
    await expect(invoke(2)).to.be.revertedWithCustomError(...violation(roles));
    await expect(invoke(1025)).to.be.revertedWithCustomError(
      ...violation(roles),
    );
  });

  it("stores and enforces a Zip next to a tuple check (Integrity rejects it)", async () => {
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
    await expect(storeValidated(tree)).to.be.revertedWithCustomError(
      roles,
      "UnsuitableChildTypeTree",
    );
    await store(tree);
    await expect(invoke([[1, 2], [7, 7], "hi"])).to.not.be.revert(ethers);
    await expect(invoke([[1, 2], [7, 8], "hi"])).to.be.revertedWithCustomError(
      ...violation(roles),
    );
  });

  it("refuses to pack a tree the check rejects (Zip among parameters)", async () => {
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
    expect(() => checkAndPack(flattenCondition(bypass) as any)).to.throw(
      "rejected",
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
    await expect(invoke([1, 2], 5)).to.not.be.revert(ethers);
    await expect(invoke([1, 2], 999)).to.be.revertedWithCustomError(
      ...violation(roles),
    );
    // array elements are values, not offsets
    await expect(invoke([32, 5], 999)).to.be.revertedWithCustomError(
      ...violation(roles),
    );
  });
});
