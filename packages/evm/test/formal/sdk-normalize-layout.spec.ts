/**
 * The SDK's `normalizeCondition` must not change where a condition reads its
 * parameters. Its Lean proof (formal/Normalize) is about decoded values; this
 * checks the calldata side on the contract (`MockEvaluator`: Integrity → pack
 * → unpack → evaluate): the normalized tree accepts exactly the calldata the
 * input tree accepts.
 *
 * The random version of this check is `GAP_NORMALIZE=1` in
 * integrity-gaps.spec.ts.
 */
import { expect } from "chai";
import { AbiCoder, ContractFactory, concat, hexlify } from "ethers";
import hre, { network } from "hardhat";

import { normalizeCondition } from "../../../sdk/src/main/condition/normalize/index.js";
import { Encoding, Operator, flattenCondition } from "../utils.js";

const abi = AbiCoder.defaultAbiCoder();
const word = (n: number) => abi.encode(["uint256"], [n]);

const eq = (n: number) => ({
  paramType: Encoding.Static,
  operator: Operator.EqualTo,
  compValue: word(n),
});
const tuple = (...children: any[]) => ({
  paramType: Encoding.Tuple,
  operator: Operator.Matches,
  children,
});
/** Calldata with a checked 4-byte selector. */
const call = (selector: string, ...children: any[]) => ({
  paramType: Encoding.AbiEncoded,
  operator: Operator.Matches,
  compValue: concat(["0x0004", selector]),
  children,
});
const or = (...children: any[]) => ({
  paramType: Encoding.None,
  operator: Operator.Or,
  children,
});

describe("SDK normalizeCondition keeps the calldata layout", function () {
  let evaluator: any;

  before(async function () {
    const { ethers } = await network.create();
    const [signer] = await ethers.getSigners();
    const lib = async (name: string) => {
      const { bytecode } = await hre.artifacts.readArtifact(name);
      const c = await new ContractFactory([], bytecode, signer).deploy();
      return c.getAddress();
    };
    evaluator = await (
      await ethers.getContractFactory("MockEvaluator", {
        libraries: {
          CustomConditionChecker: await lib("CustomConditionChecker"),
          WithinRatioChecker: await lib("WithinRatioChecker"),
        },
      })
    ).deploy();
  });

  const passes = async (tree: any, data: string) =>
    Number(await evaluator.evaluate(data, flattenCondition(tree))) === 0;

  async function expectSameVerdicts(tree: any, calldata: string[]) {
    const normalized = normalizeCondition(structuredClone(tree));
    for (const data of calldata) {
      expect(await passes(normalized, data), data).to.equal(
        await passes(tree, data),
      );
    }
  }

  it("call variants with a struct of a different width", async function () {
    // f((uint256) t, uint256 x) or g((uint256, uint256) t)
    const f = "0x11111111";
    const g = "0x22222222";
    const tree = or(
      call(f, tuple(eq(1)), eq(2)),
      call(g, tuple(eq(3), eq(4))),
    );
    await expectSameVerdicts(tree, [
      concat([f, word(1), word(2)]),
      concat([f, word(1), word(9)]),
      // the word after f's parameters is where a wider t would end
      concat([f, word(1), word(9), word(2)]),
      concat([g, word(3), word(4)]),
    ]);
  });

  it("leaves a Zip's fields and plucked arrays as written", async function () {
    // f(bytes[] a, uint256[] b), every (a[i], b[i]) passes: the trailing
    // Pass field must stay, a Zip has one field per plucked array
    const pass = (paramType: Encoding) => ({ paramType, operator: Operator.Pass });
    const pluck = (slot: number, el: Encoding) => ({
      paramType: Encoding.Array,
      operator: Operator.Pluck,
      compValue: "0x0" + slot,
      children: [pass(el)],
    });
    const zip = {
      paramType: Encoding.None,
      operator: Operator.ZipEvery,
      compValue: "0x0102",
      children: [tuple(pass(Encoding.Dynamic), pass(Encoding.Static))],
    };
    const f = "0x44444444";
    const tree = {
      paramType: Encoding.None,
      operator: Operator.And,
      children: [
        call(f, pluck(1, Encoding.Dynamic), pluck(2, Encoding.Static)),
        zip,
      ],
    };
    const data = concat([f, abi.encode(["bytes[]", "uint256[]"], [["0xaa"], [7]])]);
    await expectSameVerdicts(tree, [hexlify(data)]);
  });
});
