import { after, before, describe, it } from "node:test";
import { network } from "hardhat";
import { encodeAbiParameters, parseAbiParameters } from "viem";
import type { Hex } from "viem";
import type { GetContractReturnType } from "@nomicfoundation/hardhat-viem/types";
import type { ArtifactMap } from "hardhat/types/artifacts";

import { linkIntegrity } from "../setup.js";
import { Encoding as E, Operator as O, type ConditionFlat } from "../utils.js";

const connection = await network.create();
const { viem } = connection;

const AVATAR = "0x00000000000000000000000000000000000a7a7a" as const;

type N = {
  paramType: number;
  operator: number;
  compValue: Hex;
  children: N[];
};

const hex = (...bytes: number[]): Hex =>
  ("0x" + bytes.map((b) => b.toString(16).padStart(2, "0")).join("")) as Hex;
const word = (n: number): Hex =>
  ("0x" + n.toString(16).padStart(64, "0")) as Hex;
const fill = (length: number, byte = 0xab): Hex =>
  ("0x" + byte.toString(16).padStart(2, "0").repeat(length)) as Hex;

const node = (
  paramType: number,
  operator: number,
  compValue: Hex = "0x",
  children: N[] = [],
): N => ({ paramType, operator, compValue, children });

const pass = (paramType: number, ...children: N[]) =>
  node(paramType, O.Pass, "0x", children);
const S = pass(E.Static);
const call = (...children: N[]) =>
  node(E.AbiEncoded, O.Matches, "0x", children);
const tuple = (...children: N[]) => pass(E.Tuple, ...children);
const or = (...children: N[]) => node(E.None, O.Or, "0x", children);
const eq = (n: number) => node(E.Static, O.EqualTo, word(n));
const eqAvatar = () => node(E.Static, O.EqualToAvatar);
const pluck = (slot: number) => node(E.Static, O.Pluck, hex(slot));

function bfs(root: N): [N, number][] {
  const queue: [N, number][] = [[root, 0]];
  for (let i = 0; i < queue.length; i++) {
    for (const child of queue[i][0].children) queue.push([child, i]);
  }
  return queue;
}

const flatten = (root: N): ConditionFlat[] =>
  bfs(root).map(([n, parent]) => ({
    parent,
    paramType: n.paramType,
    operator: n.operator,
    compValue: n.compValue,
  }));

const repeat = (count: number, fn: (i: number) => N) =>
  Array.from({ length: count }, (_, i) => fn(i));

describe("Unpacker Gas Benchmark", () => {
  let mock: GetContractReturnType<ArtifactMap["MockPackerUnpacker"]["abi"]>;

  before(async () => {
    mock = await viem.deployContract(
      "MockPackerUnpacker",
      [],
      await linkIntegrity(viem),
    );
    await mock.write.setAvatar([AVATAR]);
  });

  after(async () => {
    await connection.close();
  });

  it("measures unpackGas across scenarios", async () => {
    const dynBytes = encodeAbiParameters(parseAbiParameters("bytes"), [
      fill(68),
    ]);

    const cases: [string, N][] = [
      ["1 node (Pass)", pass(E.None)],
      ["5 nodes (call: 4x Static EqualTo)", call(eq(1), eq(2), eq(3), eq(4))],
      [
        "5 nodes (call: 4x EqualToAvatar)",
        call(eqAvatar(), eqAvatar(), eqAvatar(), eqAvatar()),
      ],
      [
        "21 nodes (Or of 4x 4-arg calls, mixed)",
        or(
          ...repeat(4, (i) =>
            call(
              eq(i * 10 + 1),
              eqAvatar(),
              S,
              node(E.Static, O.GreaterThan, word(i)),
            ),
          ),
        ),
      ],
      [
        "61 nodes (Or of 12x 4-arg calls, EqualTo)",
        or(
          ...repeat(12, (i) =>
            call(eq(i * 4 + 1), eq(i * 4 + 2), eq(i * 4 + 3), eq(i * 4 + 4)),
          ),
        ),
      ],
      [
        "61 nodes (Or of 12x 4-arg calls, 1x Avatar/branch)",
        or(
          ...repeat(12, (i) =>
            call(eqAvatar(), eq(i * 3 + 1), eq(i * 3 + 2), S),
          ),
        ),
      ],
      [
        "121 nodes (Or of 24x 4-arg calls, EqualTo)",
        or(
          ...repeat(24, (i) =>
            call(eq(i * 4 + 1), eq(i * 4 + 2), eq(i * 4 + 3), eq(i * 4 + 4)),
          ),
        ),
      ],
      [
        "121 nodes (Or of 24x 4-arg calls, 1x Avatar/branch)",
        or(
          ...repeat(24, (i) =>
            call(eqAvatar(), eq(i * 3 + 1), eq(i * 3 + 2), S),
          ),
        ),
      ],
      [
        "121 nodes (balanced 3-ary depth 4, Tuple + EqualTo)",
        (() => {
          const build = (d: number): N =>
            d === 0
              ? eq(7)
              : tuple(build(d - 1), build(d - 1), build(d - 1));
          return build(4);
        })(),
      ],
      [
        "25 nodes (nested AbiEncoded + Dynamic + Slice + Bitmask + Pluck)",
        or(
          ...repeat(3, (i) =>
            call(
              pluck(i),
              node(E.Dynamic, O.EqualTo, dynBytes),
              node(E.Static, O.Slice, "0x000004", [
                node(E.Static, O.Bitmask, "0x0000ffffffff00000001"),
              ]),
              node(
                E.AbiEncoded,
                O.Matches,
                "0x0004a9059cbb",
                [eqAvatar(), eq(100)],
              ),
            ),
          ),
        ),
      ],
      [
        "1024 nodes (call with 1023x Static Pass)",
        call(...repeat(1023, () => S)),
      ],
    ];

    const results: Record<
      string,
      { nodes: number; gas: number; perNode: number }
    > = {};
    for (const [label, tree] of cases) {
      const flat = flatten(tree);
      const packed = await mock.read.packUnchecked([flat]);
      const gas = Number(await mock.read.unpackGas([packed]));
      const nodes = flat.length;
      results[label] = {
        nodes,
        gas,
        perNode: Math.round((gas / nodes) * 10) / 10,
      };
    }

    console.log("BENCHMARK_JSON:" + JSON.stringify(results));
  });
});
