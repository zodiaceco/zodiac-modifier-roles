import assert from "node:assert/strict";
import { after, before, describe, it } from "node:test";
import { network } from "hardhat";
import { encodeAbiParameters, pad, parseAbiParameters, toHex } from "viem";
import type { Hex } from "viem";
import type { GetContractReturnType } from "@nomicfoundation/hardhat-viem/types";
import type { ArtifactMap } from "hardhat/types/artifacts";

import { toFlatNodes } from "../../../sdk/src/main/condition/checkStored.js";
import { packConditions } from "../../../sdk/src/main/condition/packConditions.js";
import { linkIntegrity } from "../setup.js";
import { Encoding as E, Operator as O, type ConditionFlat } from "../utils.js";

const connection = await network.create();
const { viem } = connection;

const AVATAR = "0x00000000000000000000000000000000000a7a7a" as const;

// ---------------------------------------------------------------------------
// Trees
// ---------------------------------------------------------------------------

type N = {
  paramType: number;
  operator: number;
  compValue: Hex;
  children: N[];
};

/** A node as the unpacker returns it. */
type Unpacked = {
  parent: number;
  encoding: number;
  operator: number;
  compValue: Hex;
  leadingBytes: number;
  inlineSize: number;
};

const hex = (...bytes: number[]): Hex =>
  ("0x" + bytes.map((b) => b.toString(16).padStart(2, "0")).join("")) as Hex;
const fill = (length: number, byte = 0xab): Hex =>
  ("0x" + byte.toString(16).padStart(2, "0").repeat(length)) as Hex;
const word = (n: number): Hex =>
  ("0x" + n.toString(16).padStart(64, "0")) as Hex;
const cat = (...parts: string[]): Hex =>
  ("0x" + parts.map((p) => p.replace(/^0x/, "")).join("")) as Hex;
const byteLength = (data: string) => (data.length - 2) / 2;

const node = (
  paramType: number,
  operator: number,
  compValue: Hex = "0x",
  children: N[] = [],
): N => ({ paramType, operator, compValue, children });

const pass = (paramType: number, ...children: N[]) =>
  node(paramType, O.Pass, "0x", children);
const S = pass(E.Static);
const D = pass(E.Dynamic);
const call = (...children: N[]) =>
  node(E.AbiEncoded, O.Matches, "0x", children);
const tuple = (...children: N[]) => pass(E.Tuple, ...children);
const and = (...children: N[]) => node(E.None, O.And, "0x", children);
const pluck = (slot: number) => node(E.Static, O.Pluck, hex(slot));
const repeat = (count: number, n: N) => Array.from({ length: count }, () => n);

/** In BFS order: `[node, index of its parent]`. */
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

// ---------------------------------------------------------------------------
// The format, restated
// ---------------------------------------------------------------------------

/** A Zip is evaluated at the arrays in its slots, not where it sits. */
const isZip = (n: N) => n.operator === O.ZipSome || n.operator === O.ZipEvery;

/**
 * A node is inlined (encoded in place) unless something in it is dynamic.
 * A Zip is not inlined, and its parent does not count it.
 */
const isInlined = (n: N): boolean =>
  !isZip(n) &&
  ![E.Dynamic, E.Array, E.AbiEncoded].includes(n.paramType) &&
  n.children.every((child) => isZip(child) || isInlined(child));

/**
 * The size stored for a node: its encoded size if inlined, else 0. A word
 * is 32 bytes; And / Or (None) take the size of their first child that has
 * one; anything else is the sum of its children.
 */
const size = (n: N): number => {
  if (!isInlined(n)) return 0;
  if (n.paramType === E.Static) return 32;
  const sizes = n.children.map(size);
  return n.paramType === E.None
    ? (sizes.find((s) => s > 0) ?? 0)
    : sizes.reduce((sum, s) => sum + s, 0);
};

/** What `root` must unpack to. */
const model = (root: N): Unpacked[] =>
  bfs(root).map(([n, parent]) => {
    const isCall = n.paramType === E.AbiEncoded;
    // nested calldata: 2 bytes of leading byte count (4 if not given), then
    // the bytes to compare them with
    const leading = isCall && n.compValue === "0x" ? "0x0004" : n.compValue;
    // EqualTo on a value that is not inlined: compValue is `abi.encode`
    // output, stored without its leading offset
    const stripped = (
      n.operator === O.EqualTo && !isInlined(n)
        ? "0x" + n.compValue.slice(2 + 64)
        : n.compValue
    ) as Hex;
    return {
      parent,
      // the ether value reads no calldata: None to the evaluator
      encoding: n.paramType === E.EtherValue ? E.None : n.paramType,
      // EqualToAvatar becomes EqualTo the avatar at the time of unpacking
      operator: n.operator === O.EqualToAvatar ? O.EqualTo : n.operator,
      compValue:
        n.operator === O.EqualToAvatar
          ? pad(AVATAR, { size: 32 })
          : isCall
            ? (("0x" + leading.slice(6)) as Hex)
            : stripped,
      leadingBytes: isCall ? parseInt(leading.slice(2, 6), 16) : 0,
      inlineSize: size(n),
    };
  });

/** One more than the highest Pluck slot: how many slots to reserve. */
const pluckCount = (root: N) =>
  Math.max(
    0,
    ...bfs(root)
      .filter(([n]) => n.operator === O.Pluck)
      .map(([n]) => parseInt(n.compValue.slice(2, 4), 16) + 1),
  );

// ---------------------------------------------------------------------------

describe("ConditionPacker / ConditionUnpacker", () => {
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

  const sdkPack = (root: N) =>
    toHex(packConditions(toFlatNodes(flatten(root))));

  async function unpack(buffer: Hex) {
    const [nodes, slots] = await mock.read.unpack([buffer]);
    return {
      slots: Number(slots),
      nodes: nodes.map(
        (n): Unpacked => ({
          parent: Number(n.parent),
          encoding: Number(n.encoding),
          operator: Number(n.operator),
          compValue: n.compValue,
          leadingBytes: Number(n.leadingBytes),
          inlineSize: Number(n.inlineSize),
        }),
      ),
    };
  }

  const expectUnpacked = async (buffer: Hex, root: N) => {
    const { nodes, slots } = await unpack(buffer);
    assert.deepEqual(nodes, model(root));
    assert.equal(slots, pluckCount(root));
    return nodes;
  };

  /** Packs and unpacks on chain, checking both references. */
  async function roundtrip(root: N) {
    const packed = await mock.read.packUnchecked([flatten(root)]);
    assert.equal(packed, sdkPack(root), "buffer, against the SDK packer");
    return { packed, nodes: await expectUnpacked(packed, root) };
  }

  describe("buffer layout", () => {
    it("packs a single node into a header and one node word", async () => {
      const { packed } = await roundtrip(pass(E.None));
      assert.equal(
        packed,
        cat(
          "0001", // node count
          "00", // pluck slots
          "00000000", // None, Pass, no children, no size, no compValue
        ),
      );
    });

    it("packs node words in BFS order, then the compValues", async () => {
      const { packed } = await roundtrip(
        call(node(E.Static, O.EqualTo, word(7)), pluck(2)),
      );
      assert.equal(
        packed,
        cat(
          "0003", // node count
          "03", // pluck slots: highest slot + 1
          // encoding << 29 | operator << 24 | children << 14 | size << 1 | hasCompValue
          "a5008001", // AbiEncoded, Matches, 2 children, compValue
          "30000041", // Static, EqualTo, 32 bytes, compValue
          "2e000041", // Static, Pluck, 32 bytes, compValue
          // each compValue: 2 bytes of length, then the bytes
          cat("0002", "0004"), // the call: 4 leading bytes, by default
          cat("0020", word(7)),
          cat("0001", "02"),
        ),
      );
    });

    it("leaves nodes without a compValue out of the compValue section", async () => {
      const { packed } = await roundtrip(
        tuple(node(E.Static, O.Bitmask, "0xaaaa"), S, pluck(0)),
      );
      assert.equal(
        packed,
        cat(
          "0004",
          "01",
          "6000c0c0", // Tuple, Pass, 3 children, 96 bytes
          "35000041", // Static, Bitmask, 32 bytes, compValue
          "20000040", // Static, Pass, 32 bytes
          "2e000041", // Static, Pluck, 32 bytes, compValue
          cat("0002", "aaaa"),
          cat("0001", "00"),
        ),
      );
    });
  });

  describe("tree", () => {
    it("keeps the nodes in BFS order, each under its parent", async () => {
      const { nodes } = await roundtrip(
        call(tuple(S, tuple(D)), S, pass(E.Array, tuple(S, S))),
      );
      assert.deepEqual(
        nodes.map((n) => n.parent),
        [0, 0, 0, 0, 1, 1, 3, 5, 6, 6],
      );
    });

    it("keeps all 32 operator codes, but EqualToAvatar", async () => {
      const codes = Array.from({ length: 32 }, (_, code) => code);
      const { nodes } = await roundtrip(
        tuple(...codes.map((code) => node(E.Static, code, word(code)))),
      );
      assert.deepEqual(
        nodes.slice(1).map((n) => n.operator),
        codes.map((code) => (code === O.EqualToAvatar ? O.EqualTo : code)),
      );
    });

    it("keeps all encodings, but EtherValue, which becomes None", async () => {
      const { nodes } = await roundtrip(
        tuple(
          pass(E.None),
          pass(E.Static),
          pass(E.Dynamic),
          pass(E.Tuple, S),
          pass(E.Array, S),
          pass(E.AbiEncoded, S),
          pass(E.EtherValue),
        ),
      );
      assert.deepEqual(
        nodes.slice(1, 8).map((n) => n.encoding),
        [E.None, E.Static, E.Dynamic, E.Tuple, E.Array, E.AbiEncoded, E.None],
      );
    });
  });

  describe("compValue", () => {
    it("keeps compValues of any length, in node order", async () => {
      const compValues = [
        fill(1),
        "0x",
        fill(33),
        "0x",
        fill(2),
        fill(64),
      ] as Hex[];
      const { nodes } = await roundtrip(
        tuple(...compValues.map((cv) => node(E.Static, O.Custom, cv))),
      );
      assert.deepEqual(
        nodes.slice(1).map((n) => n.compValue),
        compValues,
      );
    });

    it("keeps the compValue of an EqualTo on an inlined value", async () => {
      const pair = encodeAbiParameters(parseAbiParameters("uint256, uint256"), [
        1n,
        2n,
      ]);
      const { nodes } = await roundtrip(
        call(
          node(E.Static, O.EqualTo, word(1)),
          node(E.Tuple, O.EqualTo, pair, [S, S]),
        ),
      );
      assert.equal(nodes[1].compValue, word(1));
      assert.equal(nodes[2].compValue, pair);
    });

    it("drops the leading offset of an EqualTo on a value that is not inlined", async () => {
      const cases: [N, Hex][] = [
        [
          node(E.Dynamic, O.EqualTo),
          encodeAbiParameters(parseAbiParameters("bytes"), ["0xaabbcc"]),
        ],
        [
          node(E.Tuple, O.EqualTo, "0x", [S, D]),
          encodeAbiParameters(parseAbiParameters("(uint256, bytes)"), [
            [1n, "0xaabbcc"],
          ]),
        ],
        [
          node(E.Array, O.EqualTo, "0x", [S]),
          encodeAbiParameters(parseAbiParameters("uint256[]"), [[1n, 2n, 3n]]),
        ],
      ];
      for (const [n, encoded] of cases) {
        const { nodes } = await roundtrip(call({ ...n, compValue: encoded }));
        assert.equal(nodes[1].compValue, "0x" + encoded.slice(2 + 64));
      }
    });

    it("splits the compValue of nested calldata into a leading byte count and the bytes to match", async () => {
      const cases: [Hex, number, Hex][] = [
        // compValue as written, leading bytes, bytes to match
        ["0x", 4, "0x"],
        ["0x0004", 4, "0x"],
        ["0x0000", 0, "0x"],
        ["0x0004a9059cbb", 4, "0xa9059cbb"],
        [cat("0x0020", fill(32)), 32, fill(32)],
        ["0x0100", 256, "0x"],
      ];
      for (const [compValue, leadingBytes, toMatch] of cases) {
        const { nodes } = await roundtrip(
          call(node(E.AbiEncoded, O.Matches, compValue, [S])),
        );
        assert.deepEqual(
          [nodes[1].leadingBytes, nodes[1].compValue],
          [leadingBytes, toMatch],
          compValue,
        );
      }
    });

    it("replaces EqualToAvatar with EqualTo the avatar, read when unpacking", async () => {
      const { packed, nodes } = await roundtrip(
        call(node(E.Static, O.EqualToAvatar)),
      );
      assert.equal(nodes[1].operator, O.EqualTo);
      assert.equal(nodes[1].compValue, pad(AVATAR, { size: 32 }));

      // the buffer does not hold the avatar: a new one shows without repacking
      const other = "0x00000000000000000000000000000000000b0b0b" as const;
      await mock.write.setAvatar([other]);
      assert.equal(
        (await unpack(packed)).nodes[1].compValue,
        pad(other, { size: 32 }),
      );
      await mock.write.setAvatar([AVATAR]);
    });
  });

  describe("size", () => {
    const ether = pass(E.EtherValue);
    const cases: [string, N, number[]][] = [
      // sizes of all nodes, in BFS order
      ["a word", S, [32]],
      ["bytes", D, [0]],
      ["a node that reads no calldata", pass(E.None), [0]],
      ["the ether value", ether, [0]],
      ["an array", pass(E.Array, S), [0, 32]],
      ["nested calldata", call(S), [0, 32]],
      ["a tuple of words", tuple(S, S), [64, 32, 32]],
      ["a nested tuple of words", tuple(S, tuple(S, S)), [96, 32, 64, 32, 32]],
      ["a tuple with bytes in it", tuple(S, D), [0, 32, 0]],
      ["a tuple with bytes two levels down", tuple(tuple(D), S), [0, 0, 32, 0]],
      ["And over a word", and(S, S), [32, 32, 32]],
      ["And over bytes", and(D, D), [0, 0, 0]],
      ["And whose first child reads no calldata", and(ether, S), [32, 0, 32]],
      ["And over nodes that read no calldata", and(ether), [0, 0]],
      ["a tuple with an And in it", tuple(and(S, S), S), [64, 32, 32, 32, 32]],
      ["a Slice of a word", node(E.Static, O.Slice, "0x000004", [S]), [32, 32]],
      ["a Slice of bytes", node(E.Dynamic, O.Slice, "0x000004", [S]), [0, 32]],
    ];
    for (const [name, tree, sizes] of cases) {
      it(`${name}: ${sizes[0]}`, async () => {
        const { nodes } = await roundtrip(tree);
        assert.deepEqual(
          nodes.map((n) => n.inlineSize),
          sizes,
        );
      });
    }
  });

  describe("pluck slots", () => {
    const cases: [string, N, number][] = [
      ["no Pluck: none", call(S), 0],
      ["slot 0: one", call(pluck(0)), 1],
      ["slots 2 and 0: three", call(pluck(2), pluck(0)), 3],
      ["slot 254: all 255", call(pluck(254)), 255],
    ];
    for (const [name, tree, count] of cases) {
      it(name, async () => {
        const { packed } = await roundtrip(tree);
        assert.equal((await unpack(packed)).slots, count);
      });
    }
  });

  describe("field limits", () => {
    it("a compValue of 65535 bytes", async () => {
      const { nodes } = await roundtrip(
        call(node(E.Dynamic, O.Custom, fill(65535)), S),
      );
      assert.equal(byteLength(nodes[1].compValue), 65535);
    });

    it("1023 children, in a tree of more than 255 nodes", async () => {
      const tree = call(...repeat(1023, S));
      const { nodes } = await roundtrip(tree);
      assert.equal(nodes.length, 1024);
      assert.equal(
        nodes.filter((n, i) => i > 0 && n.parent === 0).length,
        1023,
      );
    });

    it("the largest inlined size, 8160 bytes", async () => {
      const tree = call(tuple(...repeat(255, S)));
      const { nodes } = await roundtrip(tree);
      assert.equal(nodes[1].inlineSize, 8160);
    });
  });

  describe("random trees", () => {
    let seed = 7;
    const random = () => {
      seed = (seed + 0x6d2b79f5) | 0;
      let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
    const int = (n: number) => Math.floor(random() * n);
    const pick = <T>(xs: T[]): T => xs[int(xs.length)];

    /** Any tree the packer takes: codes and lengths at random. */
    const randomTree = (depth: number): N => {
      const paramType = int(7);
      let operator = int(32);
      let compValue = fill(pick([0, 0, 1, 2, 3, 31, 32, 33, 64, 65]), int(256));
      // what the packer asks of a tree, besides BFS order
      if (operator === O.Pluck) compValue = hex(int(255));
      if (operator === O.EqualTo) {
        // may not be inlined: at least the offset it would drop
        if (paramType === E.AbiEncoded) operator = O.Matches;
        else if (byteLength(compValue) < 32) compValue = fill(32, int(256));
      }
      if (paramType === E.AbiEncoded && byteLength(compValue) === 1) {
        compValue = hex(0, int(256));
      }
      const children =
        depth === 0
          ? []
          : Array.from({ length: int(4) }, () => randomTree(depth - 1));
      return node(paramType, operator, compValue, children);
    };

    it("300 trees pack like the SDK packer and unpack to the model", async () => {
      for (let i = 0; i < 300; i++) {
        await roundtrip(randomTree(3));
      }
    });
  });
});
