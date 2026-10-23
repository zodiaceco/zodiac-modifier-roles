/**
 * Differential test: the SDK's `checkStored` (packages/sdk/src/main/condition/
 * checkStored.ts) against its Lean specification `ConditionCheck.checkStored`
 * (packages/evm/formal/ConditionCheck), through the Lean driver's `ck` query.
 *
 * Random flat condition arrays: type-directed trees (nested calldata,
 * variants, slices, Plucks with Zips and WithinRatio over them), the same with
 * one node mutated, and loosely structured arrays from well-formed to
 * malformed (BFS order or not, any operator and encoding including invalid
 * codes, compValues of the shapes each operator expects or not). For each array and both strictness modes, the two must give
 * the same verdict (`ok <type>`, `ns` or `none`).
 *
 * The second test checks the SDK's packer (packConditions.ts) byte for byte:
 * against the Lean model of `ConditionPacker.pack` (`pk` query) on every
 * packable array, and against the contract (`MockPackerUnpacker.packUnchecked`)
 * on arrays `checkStored` accepts.
 *
 * Needs the Lean driver: `cd formal && lake build roles-model`. Skipped when it
 * is missing. `SDK_CHECK_CASES` sets the number of arrays (default 3000),
 * `SDK_CHECK_SEED` the seed.
 */
import { expect } from "chai";
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { packConditions } from "../../../sdk/src/main/condition/packConditions.js";
import { network } from "hardhat";
import {
  checkStored,
  opsOk,
  packableB,
  tyKey,
  type FlatNode,
} from "../../../sdk/src/main/condition/checkStored.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const LEAN_BIN = path.resolve(here, "../../formal/.lake/build/bin/roles-model");
const CASES = Number(process.env.SDK_CHECK_CASES ?? 3000);
const SEED = Number(process.env.SDK_CHECK_SEED ?? 1);

function mulberry32(seed: number) {
  return () => {
    seed |= 0;
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
let rand = mulberry32(SEED);
const int = (n: number) => Math.floor(rand() * n);
const chance = (p: number) => rand() < p;
const pick = <T>(xs: readonly T[]): T => xs[int(xs.length)];
const bytes = (n: number) => Uint8Array.from({ length: n }, () => int(256));

const E = {
  None: 0,
  Static: 1,
  Dynamic: 2,
  Tuple: 3,
  Array: 4,
  Abi: 5,
  Ether: 6,
};
const O = {
  Pass: 0,
  And: 1,
  Or: 2,
  Empty: 4,
  Matches: 5,
  ArraySome: 6,
  ArrayEvery: 7,
  ArrayTailMatches: 8,
  ZipSome: 10,
  ZipEvery: 11,
  Slice: 13,
  Pluck: 14,
  EqualToAvatar: 15,
  EqualTo: 16,
  GreaterThan: 17,
  LessThan: 18,
  SGT: 19,
  SLT: 20,
  Bitmask: 21,
  Custom: 22,
  WithinRatio: 23,
  WithinAllowance: 28,
  CallWithinAllowance: 30,
};
const ALL_OPS = Object.values(O);

/** A compValue that usually fits the operator (and its encoding). */
function cvFor(op: number, enc: number, nPluck: number): Uint8Array {
  if (chance(0.08)) return bytes(pick([0, 1, 2, 3, 4, 31, 32, 33, 64]));
  const slot = () => int(Math.max(nPluck, 1) + (chance(0.1) ? 2 : 0));
  switch (op) {
    case O.Matches:
      if (enc !== E.Abi) return new Uint8Array(0);
      return pick([
        () => new Uint8Array(0),
        () => Uint8Array.from([0, 4]),
        () => Uint8Array.from([0, 4, ...bytes(4)]),
        () => Uint8Array.from([0, 0]),
        () => Uint8Array.from([0, 33, ...bytes(33)]),
      ])();
    case O.ZipSome:
    case O.ZipEvery:
      return Uint8Array.from({ length: pick([2, 2, 3, 1]) }, slot);
    case O.Slice:
      return Uint8Array.from([0, int(40), pick([1, 2, 4, 32, 0, 33])]);
    case O.Pluck:
      return Uint8Array.from([chance(0.05) ? 255 : slot()]);
    case O.EqualTo:
      return bytes(pick([32, 32, 64, 96, 128]));
    case O.GreaterThan:
    case O.LessThan:
    case O.SGT:
    case O.SLT:
      return bytes(32);
    case O.Bitmask:
      return bytes(pick([4, 6, 34, 66, 5]));
    case O.Custom:
      return bytes(pick([20, 52, 19]));
    case O.WithinRatio: {
      const head = [
        slot(),
        pick([0, 18, 27, 28]),
        slot(),
        pick([0, 6, 27]),
        ...bytes(4).map((b) => (chance(0.3) ? 0 : b)),
        ...bytes(4).map((b) => (chance(0.3) ? 0 : b)),
      ];
      const blob = () => {
        const n = pick([0, 0, 5, 20, 24]);
        return [n, ...bytes(n)];
      };
      return Uint8Array.from([
        ...head,
        ...(chance(0.5) ? [] : chance(0.5) ? blob() : [...blob(), ...blob()]),
      ]);
    }
    case O.WithinAllowance:
      return bytes(pick([32, 34, 54, 53]));
    case O.CallWithinAllowance:
      return bytes(32);
    default:
      return new Uint8Array(0);
  }
}

/** An operator that usually fits the encoding and child count. */
function opFor(enc: number, hasKids: boolean): number {
  if (chance(0.1)) return pick(ALL_OPS);
  if (chance(0.02)) return pick([3, 9, 12, 24]); // placeholder codes
  switch (enc) {
    case E.None:
      return hasKids
        ? pick([O.And, O.Or, O.And, O.Or, O.ZipSome, O.ZipEvery, O.Pass])
        : pick([
            O.Pass,
            O.Empty,
            O.WithinRatio,
            O.CallWithinAllowance,
            O.EqualTo,
          ]);
    case E.Static:
      return hasKids
        ? O.Slice
        : pick([
            O.Pass,
            O.EqualTo,
            O.GreaterThan,
            O.LessThan,
            O.SGT,
            O.SLT,
            O.Bitmask,
            O.Pluck,
            O.EqualToAvatar,
            O.WithinAllowance,
            O.Custom,
          ]);
    case E.Dynamic:
      return hasKids ? O.Slice : pick([O.Pass, O.EqualTo, O.Bitmask, O.Custom]);
    case E.Tuple:
      return pick([O.Matches, O.Pass, O.EqualTo, O.Custom]);
    case E.Array:
      return pick([
        O.Matches,
        O.ArraySome,
        O.ArrayEvery,
        O.ArrayTailMatches,
        O.Pass,
        O.EqualTo,
        O.Pluck,
      ]);
    case E.Abi:
      return pick([O.Matches, O.Matches, O.Pass]);
    case E.Ether:
      return pick([
        O.Pass,
        O.EqualTo,
        O.GreaterThan,
        O.LessThan,
        O.Pluck,
        O.WithinAllowance,
      ]);
    default:
      return pick(ALL_OPS);
  }
}

/** A random tree shape (children counts in BFS order), then node contents. */
function genFlat(): FlatNode[] {
  const n = 1 + int(chance(0.7) ? 8 : 16);
  const parents = [0];
  // BFS: parents non-decreasing and earlier
  let p = 0;
  for (let j = 1; j < n; j++) {
    if (chance(0.45) && p + 1 < j) p += 1 + (chance(0.2) ? int(j - p - 1) : 0);
    parents.push(Math.min(p, j - 1));
  }
  if (chance(0.06)) parents[1 + int(Math.max(n - 1, 1))] = int(n + 1); // break BFS
  const hasKids = (i: number) => parents.some((q, j) => j > 0 && q === i);
  const encs = parents.map((_, i) => {
    if (chance(0.02)) return 7; // invalid code
    if (i === 0) return pick([E.Abi, E.Abi, E.None, E.None, E.Tuple, E.Ether]);
    return hasKids(i)
      ? pick([E.Tuple, E.Array, E.Abi, E.None, E.None, E.Static, E.Dynamic])
      : pick([
          E.Static,
          E.Static,
          E.Dynamic,
          E.None,
          E.Ether,
          E.Tuple,
          E.Array,
        ]);
  });
  const ops = encs.map((e, i) => opFor(e, hasKids(i)));
  const nPluck = ops.filter((o) => o === O.Pluck).length;
  return parents.slice(0, n).map((parent, i) => ({
    parent,
    paramType: encs[i],
    operator: ops[i],
    compValue: cvFor(ops[i], encs[i], nPluck),
  }));
}

// ---------------------------------------------------------------------------
// Type-directed trees (mostly accepted), flattened in BFS order
// ---------------------------------------------------------------------------

type T =
  | { k: "s" }
  | { k: "d" }
  | { k: "t"; ts: T[] }
  | { k: "a"; t: T }
  | { k: "c"; lb: number; ts: T[] };
type N = { e: number; o: number; cv: Uint8Array; ch: N[] };

const isStaticT = (t: T): boolean =>
  t.k === "s" || (t.k === "t" && t.ts.every(isStaticT));
const node = (
  e: number,
  o: number,
  ch: N[] = [],
  cv = new Uint8Array(0),
): N => ({ e, o, cv, ch });

function randT(depth: number): T {
  const r = int(depth > 0 ? 5 : 2);
  if (r === 0) return { k: "s" };
  if (r === 1) return { k: "d" };
  if (r === 2)
    return {
      k: "t",
      ts: Array.from({ length: 1 + int(3) }, () => randT(depth - 1)),
    };
  if (r === 3) return { k: "a", t: randT(depth - 1) };
  return {
    k: "c",
    lb: pick([0, 4, 4, 2]),
    ts: Array.from({ length: 1 + int(2) }, () => randT(depth - 1)),
  };
}

/** Pluck slots handed out while generating one tree. */
let slots: { slot: number; t: T }[] = [];

/** A plain node describing type `t` (`Pass`-like children for containers). */
function passFor(t: T): N {
  switch (t.k) {
    case "s":
      return node(E.Static, O.Pass);
    case "d":
      return node(E.Dynamic, O.Pass);
    case "t":
      return node(E.Tuple, O.Matches, t.ts.map(passFor));
    case "a":
      return node(E.Array, O.Pass, [passFor(t.t)]);
    case "c":
      return node(
        E.Abi,
        O.Matches,
        t.ts.map(passFor),
        t.lb ? Uint8Array.from([0, t.lb, ...bytes(t.lb)]) : new Uint8Array(0),
      );
  }
}

function genT(t: T, depth: number): N {
  if (depth < 3 && chance(0.12)) {
    // And/Or over two descriptions (+ maybe an ether check), or a variant
    const kids = [genT(t, depth + 1), genT(t, depth + 1)];
    if (chance(0.3))
      kids.push(
        node(
          E.Ether,
          pick([O.LessThan, O.GreaterThan, O.EqualTo]),
          [],
          bytes(32),
        ),
      );
    if ((t.k === "d" || t.k === "c") && chance(0.4))
      kids.push(genT({ k: "c", lb: 4, ts: [{ k: "s" }] }, depth + 1));
    return node(E.None, pick([O.And, O.Or]), kids);
  }
  switch (t.k) {
    case "s": {
      const r = int(9);
      if (r === 0) return node(E.Static, O.EqualTo, [], bytes(32));
      if (r === 1)
        return node(
          E.Static,
          pick([O.GreaterThan, O.LessThan, O.SGT, O.SLT]),
          [],
          bytes(32),
        );
      if (r === 2)
        return node(E.Static, O.Bitmask, [], bytes(pick([4, 6, 34])));
      if (r === 3)
        return node(
          E.Static,
          O.Slice,
          [node(E.Static, O.EqualTo, [], bytes(32))],
          Uint8Array.from([0, int(16), 1 + int(16)]),
        );
      if (r === 4) {
        const slot = slots.length;
        slots.push({ slot, t });
        return node(E.Static, O.Pluck, [], Uint8Array.from([slot]));
      }
      if (r === 5) return node(E.Static, O.WithinAllowance, [], bytes(32));
      if (r === 6) return node(E.Static, O.EqualToAvatar);
      return node(E.Static, O.Pass);
    }
    case "d": {
      const r = int(5);
      if (r === 0) return node(E.Dynamic, O.EqualTo, [], bytes(96));
      if (r === 1) return node(E.Dynamic, O.Bitmask, [], bytes(6));
      if (r === 2)
        return node(
          E.Dynamic,
          O.Slice,
          [node(E.Static, O.EqualTo, [], bytes(32))],
          Uint8Array.from([0, int(8), 1 + int(31)]),
        );
      if (r === 3) return node(E.Dynamic, O.Custom, [], bytes(20));
      return node(E.Dynamic, O.Pass);
    }
    case "t": {
      const r = int(4);
      if (r === 0)
        return node(
          E.Tuple,
          O.EqualTo,
          t.ts.map(passFor),
          bytes(isStaticT(t) ? 32 * t.ts.length : 96),
        );
      if (r === 1) return node(E.Tuple, O.Pass, t.ts.map(passFor));
      return node(
        E.Tuple,
        O.Matches,
        t.ts.map((x) => genT(x, depth + 1)),
      );
    }
    case "a": {
      const r = int(6);
      if (r === 0)
        return node(E.Array, pick([O.ArraySome, O.ArrayEvery]), [
          genT(t.t, depth + 1),
        ]);
      if (r === 1)
        return node(E.Array, O.ArrayTailMatches, [
          genT(t.t, depth + 1),
          genT(t.t, depth + 1),
        ]);
      if (r === 2)
        return node(E.Array, O.Matches, [
          genT(t.t, depth + 1),
          genT(t.t, depth + 1),
        ]);
      if (r === 3) {
        const slot = slots.length;
        slots.push({ slot, t });
        return node(E.Array, O.Pluck, [passFor(t.t)], Uint8Array.from([slot]));
      }
      return node(E.Array, O.Pass, [passFor(t.t)]);
    }
    case "c":
      return node(
        E.Abi,
        chance(0.9) ? O.Matches : O.Pass,
        t.ts.map((x) => genT(x, depth + 1)),
        t.lb
          ? Uint8Array.from([0, t.lb, ...bytes(t.lb)])
          : chance(0.5)
            ? Uint8Array.from([0, 4])
            : new Uint8Array(0),
      );
  }
}

function genTree(): N {
  slots = [];
  const args = Array.from({ length: 1 + int(3) }, () => randT(2));
  const argNodes = args.map((t) => genT(t, 2));
  // often: plucked arrays and words directly among the arguments
  if (chance(0.5)) {
    const el = randT(1);
    for (let k = 0; k < 2; k++) {
      const t: T = { k: "a", t: el };
      const slot = slots.length;
      slots.push({ slot, t });
      args.push(t);
      argNodes.push(
        node(E.Array, O.Pluck, [passFor(el)], Uint8Array.from([slot])),
      );
    }
  }
  if (chance(0.3)) {
    for (let k = 0; k < 2; k++) {
      const slot = slots.length;
      slots.push({ slot, t: { k: "s" } });
      args.push({ k: "s" });
      argNodes.push(node(E.Static, O.Pluck, [], Uint8Array.from([slot])));
    }
  }
  const root = node(
    E.Abi,
    O.Matches,
    argNodes,
    Uint8Array.from([0, 4, ...bytes(4)]),
  );
  const extra: N[] = [];
  const arrays = slots.filter((x) => x.t.k === "a");
  if (arrays.length >= 2 && chance(0.8)) {
    const [a, b] = [arrays[0], arrays[arrays.length - 1]];
    const fields = [a, b].map((x) => genT((x.t as { t: T }).t, 2));
    extra.push(
      node(
        E.None,
        pick([O.ZipSome, O.ZipEvery]),
        [node(E.Tuple, O.Matches, fields)],
        Uint8Array.from([a.slot, b.slot]),
      ),
    );
  }
  const words = slots.filter((x) => x.t.k === "s");
  if (words.length >= 2 && chance(0.6)) {
    const cv = Uint8Array.from([
      words[0].slot,
      18,
      words[1].slot,
      6,
      0,
      0,
      0,
      1,
      0,
      0,
      0,
      2,
    ]);
    extra.push(node(E.None, O.WithinRatio, [], cv));
  }
  if (chance(0.15)) extra.push(node(E.Ether, O.LessThan, [], bytes(32)));
  return extra.length ? node(E.None, O.And, [root, ...extra]) : root;
}

function flattenN(root: N): FlatNode[] {
  const out: FlatNode[] = [];
  const queue: { n: N; parent: number }[] = [{ n: root, parent: 0 }];
  while (queue.length) {
    const { n, parent } = queue.shift()!;
    out.push({ parent, paramType: n.e, operator: n.o, compValue: n.cv });
    const i = out.length - 1;
    for (const c of n.ch) queue.push({ n: c, parent: i });
  }
  return out;
}

/** Changes one node: operator, encoding, compValue, or a parent. */
function mutateFlat(fs: FlatNode[]): FlatNode[] {
  const out = fs.map((f) => ({ ...f }));
  const i = int(out.length);
  switch (int(5)) {
    case 0:
      out[i].operator = pick(ALL_OPS);
      break;
    case 1:
      out[i].paramType = int(7);
      break;
    case 2:
      out[i].compValue = cvFor(out[i].operator, out[i].paramType, 3);
      break;
    case 3: {
      const b = out[i].compValue.slice();
      if (b.length)
        b[int(Math.min(b.length, 4))] = pick([
          0, 1, 2, 27, 28, 32, 33, 254, 255,
        ]);
      out[i].compValue = b;
      break;
    }
    default:
      // a parent at or before the node (itself included); the root's parent
      // field is ignored by the check
      out[i].parent = i > 0 ? int(i + 1) : int(out.length + 2);
      break;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Targeted cases: every operator with every encoding, and each rule at the
// boundaries of its limits, inside contexts that are otherwise accepted
// ---------------------------------------------------------------------------

const S = () => node(E.Static, O.Pass);
const D = () => node(E.Dynamic, O.Pass);
const SEL = () => Uint8Array.from([0, 4, ...bytes(4)]);
const call = (ch: N[]) => node(E.Abi, O.Matches, ch, SEL());
const word = (v: number) => [
  v >>> 24,
  (v >>> 16) & 255,
  (v >>> 8) & 255,
  v & 255,
];

/** A WithinRatio compValue: slots, decimals, ratios, then raw adapter bytes. */
const wrCv = (
  s0: number,
  d0: number,
  s1: number,
  d1: number,
  min: number,
  max: number,
  tail: number[] = [],
) => Uint8Array.from([s0, d0, s1, d1, ...word(min), ...word(max), ...tail]);
/** An adapter blob of `n` bytes (`n` in the length byte, `m` bytes follow). */
const blob = (n: number, m = n) => [n, ...bytes(m)];

/**
 * Calldata with static Plucks in slots 0 and 1 and array Plucks (of statics)
 * in slots 2 and 3, then `args`; with `extras`, the root is
 * `And(calldata, ...extras)`.
 */
function withPlucks(args: N[], extras: N[] = [], elem: () => N = S): N {
  const root = call([
    node(E.Static, O.Pluck, [], Uint8Array.from([0])),
    node(E.Static, O.Pluck, [], Uint8Array.from([1])),
    node(E.Array, O.Pluck, [elem()], Uint8Array.from([2])),
    node(E.Array, O.Pluck, [elem()], Uint8Array.from([3])),
    ...args,
  ]);
  return extras.length ? node(E.None, O.And, [root, ...extras]) : root;
}

const zip = (op: number, slots: number[], fields: N[]) =>
  node(E.None, op, [node(E.Tuple, O.Matches, fields)], Uint8Array.from(slots));

/** A compValue each operator accepts (in the `withPlucks` context). */
function goodCv(op: number): Uint8Array {
  switch (op) {
    case O.Slice:
      return Uint8Array.from([0, 0, 4]);
    case O.Pluck:
      return Uint8Array.from([7]);
    case O.ZipSome:
    case O.ZipEvery:
      return Uint8Array.from([2, 3]);
    case O.EqualTo:
    case O.GreaterThan:
    case O.LessThan:
    case O.SGT:
    case O.SLT:
    case O.WithinAllowance:
    case O.CallWithinAllowance:
      return bytes(32);
    case O.Bitmask:
      return bytes(4);
    case O.Custom:
      return bytes(20);
    case O.WithinRatio:
      return wrCv(0, 18, 1, 6, 1, 2);
    default:
      return new Uint8Array(0);
  }
}

type Case = { fs: FlatNode[]; modes: number[] };

function targetedCases(): Case[] {
  const out: Case[] = [];
  const add = (root: N, modes = [0, 1]) =>
    out.push({ fs: flattenN(root), modes });
  const addFlat = (fs: FlatNode[], modes = [0, 1]) => out.push({ fs, modes });
  /** `x` as an argument and as a sibling of the calldata under `And`. */
  const both = (x: () => N) => {
    add(withPlucks([x()]));
    add(withPlucks([], [x()]));
  };

  // every operator (and placeholder codes) with every encoding (and an
  // invalid one), with no, one or two children, and a few compValues
  const kidSets: (() => N[])[] = [
    () => [],
    () => [S()],
    () => [S(), S()],
    () => [node(E.Tuple, O.Matches, [S(), S()])],
  ];
  for (const op of [...ALL_OPS, 3, 31])
    for (let e = 0; e <= 7; e++)
      for (const kids of kidSets)
        for (const cv of [
          () => goodCv(op),
          () => new Uint8Array(0),
          () => bytes(1),
          () => bytes(32),
        ])
          both(() => node(e, op, kids(), cv()));

  // compValue lengths at and around each operator's limits
  const lens = (
    mk: (cv: Uint8Array) => N,
    ls: number[],
    fill: (n: number) => Uint8Array = bytes,
  ) => {
    for (const l of ls) both(() => mk(fill(l)));
  };
  lens((cv) => node(E.Static, O.Custom, [], cv), [19, 20, 65535, 65536]);
  lens((cv) => node(E.Dynamic, O.EqualTo, [], cv), [32, 63, 64, 65535]);
  lens(
    (cv) => node(E.Tuple, O.EqualTo, [S(), D()], cv),
    [31, 32, 63, 64, 65535],
  );
  lens((cv) => node(E.Tuple, O.EqualTo, [S()], cv), [31, 32, 33]);
  lens((cv) => node(E.Array, O.EqualTo, [S()], cv), [31, 32, 63, 64]);
  lens((cv) => node(E.Dynamic, O.Bitmask, [], cv), [2, 4, 65534]);
  for (const e of [E.Static, E.Ether])
    for (const b of [0, 27, 28])
      lens(
        (cv) => node(e, O.WithinAllowance, [], cv),
        [31, 32, 33, 34, 53, 54, 55, 65535],
        (n) => {
          const cv = bytes(n);
          if (n > 33) [cv[32], cv[33]] = chance(0.5) ? [b, 0] : [0, b];
          return cv;
        },
      );
  for (const l of [0, 31, 32, 33])
    both(() => node(E.None, O.CallWithinAllowance, [], bytes(l)));
  for (const lb of [0, 1, 4, 31, 32, 33])
    for (const extra of [0, 1, -1])
      both(() =>
        node(
          E.Abi,
          O.Matches,
          [S()],
          Uint8Array.from([0, lb, ...bytes(Math.max(lb + extra, 0))]),
        ),
      );
  for (const e of [E.Static, E.Dynamic])
    for (const size of [0, 1, 31, 32, 33])
      both(() =>
        node(
          e,
          O.Slice,
          [node(E.Static, O.EqualTo, [], bytes(32))],
          Uint8Array.from([0, int(4), size]),
        ),
      );
  for (const slot of [253, 254, 255])
    for (const e of [E.Static, E.Ether, E.Array])
      both(() =>
        node(e, O.Pluck, e === E.Array ? [S()] : [], Uint8Array.from([slot])),
      );
  // operators that take no compValue (or no children), with one
  for (const op of [O.And, O.Or])
    both(() => node(E.None, op, [S()], bytes(pick([1, 32]))));
  for (const op of [O.ArraySome, O.ArrayEvery, O.ArrayTailMatches]) {
    both(() => node(E.Array, op, [S()], bytes(1)));
    both(() => node(E.Array, op, [S(), S()]));
  }
  for (const e of [E.None, E.Static, E.Tuple, E.Array, E.Ether, E.Abi])
    both(() =>
      node(
        e,
        O.Custom,
        e === E.Tuple || e === E.Array || e === E.Abi ? [S()] : [],
        bytes(20),
      ),
    );

  // prefix siblings: checks of the first fields of one tuple or call
  // (pruned Matches), next to longer, closed or static ones
  const ptup = (o: number, ...ch: N[]) => node(E.Tuple, o, ch);
  const pcall = (o: number, ...ch: N[]) => node(E.Abi, o, ch);
  const eqS = () => node(E.Static, O.EqualTo, [], bytes(32));
  for (const lop of [O.And, O.Or]) {
    const lg = (...ch: N[]) => node(E.None, lop, ch);
    // dynamic tuples: (bytes, uint) and (bytes, uint, uint)
    both(() => lg(ptup(O.Matches, D(), eqS()), ptup(O.Matches, D(), S(), eqS())));
    both(() => lg(ptup(O.Matches, D()), ptup(O.EqualTo, D(), S())));
    both(() => lg(ptup(O.EqualTo, D(), S()), ptup(O.Matches, D())));
    both(() => lg(ptup(O.EqualTo, D()), ptup(O.EqualTo, D(), S())));
    // static tuples of different lengths (inlined: never prefixes)
    both(() => lg(ptup(O.Matches, eqS()), ptup(O.Matches, S(), eqS())));
    // a dynamic prefix of a tuple that is static
    both(() => lg(ptup(O.Matches, D()), ptup(O.Matches, D(), S())));
    // calls with the same and different leading bytes
    both(() => lg(pcall(O.Matches, eqS()), pcall(O.Matches, S(), D())));
    both(() => lg(pcall(O.Matches, eqS()), pcall(O.Pass, S(), D())));
    // nested: the field of a tuple is a prefix
    both(() =>
      lg(
        ptup(O.Matches, ptup(O.Matches, D()), S()),
        ptup(O.Matches, ptup(O.Matches, D(), eqS()), S()),
      ),
    );
  }
  // array elements: the template must be the most specific
  for (const op of [O.Matches, O.ArraySome, O.ArrayEvery, O.ArrayTailMatches]) {
    both(() => node(E.Array, op, [ptup(O.Matches, D(), eqS()), ptup(O.Matches, D())]));
    both(() => node(E.Array, op, [ptup(O.Matches, D()), ptup(O.Matches, D(), eqS())]));
  }
  // navigation below an operator that reads its whole value
  both(() => node(E.Tuple, O.EqualTo, [ptup(O.Matches, S())], bytes(32)));
  both(() => node(E.Tuple, O.EqualTo, [node(E.None, O.Or, [S()])], bytes(32)));
  both(() => node(E.Abi, O.Pass, [ptup(O.Matches, D())]));

  // inlined sizes around 8191 bytes, and child counts around 1023
  const statics = (k: number) => Array.from({ length: k }, S);
  for (const k of [255, 256])
    add(call([node(E.Tuple, O.Matches, statics(k))]), [1]);
  add(
    call([
      node(E.Tuple, O.Matches, [
        node(E.None, O.And, [node(E.Ether, O.Pass), S()]),
        ...statics(255),
      ]),
    ]),
    [1],
  );
  add(call(statics(1023)), [1]);
  add(call(statics(1024)), [1]);

  // WithinRatio compValues around each rule
  const wrs: Uint8Array[] = [];
  for (const [d0, d1] of [
    [0, 0],
    [27, 27],
    [28, 0],
    [0, 28],
  ])
    wrs.push(wrCv(0, d0, 1, d1, 1, 2));
  for (const [mn, mx] of [
    [0, 0],
    [0, 5],
    [5, 0],
    [1, 2],
    [2, 1],
    [3, 3],
    [0x01000000, 0x00ffffff],
    [0x00ffffff, 0x01000000],
  ])
    wrs.push(wrCv(0, 18, 1, 6, mn, mx));
  const tails = [
    [0],
    [0, 0],
    [0, 0, 0],
    blob(1),
    blob(5),
    blob(19),
    blob(20),
    blob(21),
    blob(255),
    blob(20, 19),
    blob(20, 21),
    [...blob(20), 0],
    [0, ...blob(20)],
    [...blob(20), ...blob(32)],
    [...blob(20), ...blob(5)],
    [...blob(20), ...blob(20, 19)],
    [...blob(20), ...blob(20), 0],
    [...blob(20), ...blob(20, 21)],
  ];
  for (const t of tails) wrs.push(wrCv(0, 18, 1, 6, 1, 2, t));
  wrs.push(wrCv(0, 18, 1, 6, 1, 2).slice(0, 11));
  for (const cv of wrs)
    add(withPlucks([], [node(E.None, O.WithinRatio, [], cv)]));
  // ... over an ether Pluck, an array Pluck, a missing slot
  for (const [a, b] of [
    [0, 4],
    [4, 1],
    [0, 2],
    [3, 1],
    [0, 9],
  ])
    add(
      withPlucks(
        [],
        [
          node(E.Ether, O.Pluck, [], Uint8Array.from([4])),
          node(E.None, O.WithinRatio, [], wrCv(a, 18, b, 6, 1, 2)),
        ],
      ),
    );
  // ... in `Or` (each branch must assign the slots), over slots a Slice or a
  // non-`Matches` container reads
  for (const first of [true, false]) {
    const wr = node(E.None, O.WithinRatio, [], wrCv(0, 18, 9, 6, 1, 2));
    const other = node(E.Ether, O.Pass);
    add(
      withPlucks([], [node(E.None, O.Or, first ? [wr, other] : [other, wr])]),
    );
  }
  const pluck9 = () => node(E.Static, O.Pluck, [], Uint8Array.from([9]));
  const wr09 = () => node(E.None, O.WithinRatio, [], wrCv(0, 18, 9, 6, 1, 2));
  for (const e of [E.Static, E.Dynamic])
    add(
      withPlucks(
        [node(e, O.Slice, [pluck9()], Uint8Array.from([0, 0, 4]))],
        [wr09()],
      ),
    );
  for (const op of [O.Pass, O.Matches, O.Custom, O.EqualTo])
    add(
      withPlucks(
        [
          node(
            E.Tuple,
            op,
            [pluck9(), S()],
            op === O.Custom
              ? bytes(20)
              : op === O.EqualTo
                ? bytes(64)
                : new Uint8Array(0),
          ),
        ],
        [wr09()],
      ),
    );

  // Zips: repeated slots, Plucks below the Zip, slots of non-array Plucks
  for (const op of [O.ZipSome, O.ZipEvery]) {
    add(withPlucks([], [zip(op, [2, 3], [S(), S()])]));
    add(withPlucks([], [zip(op, [2, 2, 3], [S(), S(), S()])]));
    add(withPlucks([], [zip(op, [2, 3, 2], [S(), S(), S()])]));
    add(withPlucks([], [zip(op, [2, 3], [pluck9(), S()])]));
    add(
      withPlucks(
        [],
        [
          zip(
            op,
            [2, 3],
            [
              S(),
              node(E.Static, O.Slice, [pluck9()], Uint8Array.from([0, 0, 4])),
            ],
          ),
        ],
      ),
    );
    add(withPlucks([], [zip(op, [2, 0], [S(), S()])]));
    add(
      withPlucks(
        [],
        [
          zip(op, [2, 4], [S(), S()]),
          node(E.Ether, O.Pluck, [], Uint8Array.from([4])),
        ],
      ),
    );
    add(withPlucks([], [zip(op, [2, 9], [S(), S()])]));
    // the root's parent field pointing below the Zip
    const fs = flattenN(withPlucks([], [zip(op, [2, 3], [S(), S()])]));
    const z = fs.findIndex((f) => f.operator === op);
    for (const p of [z, z + 1, 1]) {
      const g = fs.map((f) => ({ ...f }));
      g[0].parent = p;
      addFlat(g);
    }
  }
  // Zip field types vs the arrays' element types (variants of `bytes`)
  const callS = () => call([S()]);
  const callD = () => call([D()]);
  for (const [elem, fields] of [
    [callS, [D(), D()]],
    [D, [callS(), callS()]],
    [callS, [callD(), callS()]],
    [D, [D(), node(E.None, O.Or, [D(), callS()])]],
    [S, [D(), S()]],
    [
      () => node(E.Tuple, O.Matches, [S(), D()]),
      [node(E.Tuple, O.Matches, [S(), D()]), S()],
    ],
  ] as [() => N, N[]][])
    add(withPlucks([], [zip(O.ZipSome, [2, 3], fields)], elem));

  // And/Or (in argument position and at the root) over types and Zips
  const tup = (...ts: N[]) => node(E.Tuple, O.Matches, ts);
  const kinds: (() => N)[] = [
    S,
    D,
    () => node(E.Ether, O.Pass),
    () => tup(S(), S()),
    () => tup(S(), D()),
    () => tup(tup(S())),
    () => tup(tup(D())),
    callS,
    () => zip(O.ZipSome, [2, 3], [S(), S()]),
  ];
  for (const op of [O.And, O.Or])
    for (const a of kinds)
      for (const b of kinds) {
        add(withPlucks([node(E.None, op, [a(), b()])]));
        add(withPlucks([node(E.Array, O.Matches, [a(), b()])]));
      }
  for (const op of [O.And, O.Or])
    for (const b of kinds) {
      add(node(E.None, op, [callS(), b()]));
      add(node(E.None, op, [b(), callS()]));
      add(node(E.None, op, [b(), b()]));
    }
  add(node(E.None, O.Or, [callS(), call([D()])]));

  // topology: the root's parent field, self-parents, BFS order at the end
  for (const base of [
    () => flattenN(call([node(E.Tuple, O.Matches, [S(), D()]), S()])),
    () => flattenN(withPlucks([S()], [node(E.Ether, O.Pass)])),
  ])
    for (const mod of [
      (g: FlatNode[]) => (g[0].parent = 1),
      (g: FlatNode[]) => (g[0].parent = 5),
      (g: FlatNode[]) =>
        g.push({
          parent: g.length,
          paramType: E.Static,
          operator: O.Pass,
          compValue: new Uint8Array(0),
        }),
      (g: FlatNode[]) => (g[g.length - 1].parent = g.length - 1),
      (g: FlatNode[]) => (g[1].parent = 1),
      (g: FlatNode[]) =>
        g.push({
          parent: Math.max(g[g.length - 1].parent - 1, 0),
          paramType: E.Static,
          operator: O.Pass,
          compValue: new Uint8Array(0),
        }),
      (g: FlatNode[]) =>
        g.push({
          parent: g[g.length - 1].parent + 1,
          paramType: E.Static,
          operator: O.Pass,
          compValue: new Uint8Array(0),
        }),
    ]) {
      const g = base().map((f) => ({ ...f }));
      mod(g);
      addFlat(g);
    }
  return out;
}

const hex = (b: Uint8Array) =>
  Array.from(b, (x) => x.toString(16).padStart(2, "0")).join("");
const line = (s: number, fs: FlatNode[]) =>
  `ck ${s} ` +
  fs
    .map((f) => `${f.parent}:${f.paramType}:${f.operator}:${hex(f.compValue)}`)
    .join("|");
const tsVerdict = (fs: FlatNode[], s: boolean) => {
  const v = checkStored(fs, s);
  return v === undefined
    ? "none"
    : v.kind === "noCalldata"
      ? "ns"
      : `ok ${tyKey(v.type)}`;
};

describe("SDK checkStored vs Lean ConditionCheck.checkStored", function () {
  this.timeout(0);

  it(`agrees on ${CASES} random flat arrays (both strictness modes)`, function () {
    if (!existsSync(LEAN_BIN)) this.skip();
    // the empty array is not `Packable` (the driver cannot express it)
    for (const s of [false, true])
      expect(checkStored([], s)).to.equal(undefined);
    rand = mulberry32(SEED);
    const cases: Case[] = [
      ...Array.from({ length: CASES }, () => {
        if (chance(0.3)) return genFlat();
        const fs = flattenN(genTree());
        return chance(0.35) ? mutateFlat(fs) : fs;
      }).map((fs) => ({ fs, modes: [0, 1] })),
      ...targetedCases(),
    ];
    const arrays = cases.map((c) => c.fs);
    const queries = cases.flatMap((c) => c.modes.map((s) => ({ s, fs: c.fs })));
    const res = spawnSync(LEAN_BIN, {
      input: queries.map((q) => line(q.s, q.fs)).join("\n") + "\n",
      maxBuffer: 1 << 28,
    });
    expect(res.status, String(res.stderr)).to.equal(0);
    const out = String(res.stdout).trim().split("\n");
    expect(out.length).to.equal(queries.length);

    const tally = new Map<string, number>();
    const mismatches: string[] = [];
    queries.forEach((q, i) => {
      const lean = out[i];
      const ts = tsVerdict(q.fs, q.s === 1);
      const k = `s=${q.s} ${lean.split(" ")[0]}`;
      tally.set(k, (tally.get(k) ?? 0) + 1);
      if (lean !== ts)
        mismatches.push(
          `${line(q.s, q.fs).slice(0, 4000)}\n    lean: ${lean}\n    ts:   ${ts}`,
        );
    });
    for (const [k, n] of [...tally].sort()) console.log(`      ${k}: ${n}`);
    // which part rejects, and what accepted arrays contain (s = 1)
    const why = new Map<string, number>();
    const bump = (k: string) => why.set(k, (why.get(k) ?? 0) + 1);
    for (const fs of arrays) {
      const v = checkStored(fs, true);
      if (v) {
        bump("accepted");
        for (const [name, op] of [
          ["Zip", O.ZipSome],
          ["Zip", O.ZipEvery],
          ["WithinRatio", O.WithinRatio],
          ["Slice", O.Slice],
          ["Pluck", O.Pluck],
        ] as const)
          if (fs.some((f) => f.operator === op)) bump(`accepted with ${name}`);
      } else if (
        !fs.every(
          (f) => f.paramType <= 6 && Object.values(O).includes(f.operator),
        )
      )
        bump("rejected: invalid code");
      else if (!packableB(fs)) bump("rejected: packableB");
      else if (!opsOk(fs)) bump("rejected: opsOk");
      else bump("rejected: slots or types");
    }
    for (const [k, n] of [...why].sort()) console.log(`      ${k}: ${n}`);
    for (const m of mismatches.slice(0, 5)) console.log(`      MISMATCH ${m}`);
    expect(mismatches.length).to.equal(0);
  });

  it(`packs byte for byte like ConditionPacker (${CASES} random flat arrays)`, async function () {
    if (!existsSync(LEAN_BIN)) this.skip();
    rand = mulberry32(SEED + 1);
    const arrays = Array.from({ length: CASES }, () => {
      if (chance(0.3)) return genFlat();
      const fs = flattenN(genTree());
      return chance(0.35) ? mutateFlat(fs) : fs;
    }).filter(
      (fs) =>
        fs.every(
          (f) => f.paramType <= 6 && Object.values(O).includes(f.operator),
        ) && packableB(fs),
    );
    // Lean model of the packer (with the assembly), on every packable array
    const res = spawnSync(LEAN_BIN, {
      input:
        arrays.map((fs) => line(0, fs).replace(/^ck 0 /, "pk ")).join("\n") +
        "\n",
      maxBuffer: 1 << 28,
    });
    expect(res.status, String(res.stderr)).to.equal(0);
    const out = String(res.stdout).trim().split("\n");
    expect(out.length).to.equal(arrays.length);
    const leanDiff = arrays.filter(
      (fs, i) => out[i] !== "0x" + hex(packConditions(fs)),
    );
    for (const fs of leanDiff.slice(0, 3))
      console.log(
        `      LEAN MISMATCH ${line(0, fs)}\n        ts ${hex(packConditions(fs))}`,
      );

    // the contract, on arrays checkStored accepts
    const { ethers } = await network.create();
    const mock = await (
      await ethers.getContractFactory("MockPackerUnpacker")
    ).deploy();
    const accepted = arrays
      .filter((fs) => checkStored(fs, true) !== undefined)
      .slice(0, 600);
    let chainDiff = 0;
    for (const fs of accepted) {
      const sol = await mock.packUnchecked(
        fs.map((f) => ({ ...f, compValue: "0x" + hex(f.compValue) })),
        { gasLimit: 30_000_000 },
      );
      if (sol !== "0x" + hex(packConditions(fs))) {
        if (chainDiff++ < 3)
          console.log(
            `      CHAIN MISMATCH ${line(0, fs)}\n        sol ${sol}\n        ts  0x${hex(packConditions(fs))}`,
          );
      }
    }
    console.log(
      `      ${arrays.length} packable arrays vs Lean, ${accepted.length} accepted arrays vs ConditionPacker`,
    );
    expect(leanDiff.length).to.equal(0);
    expect(chainDiff).to.equal(0);
  });
});
