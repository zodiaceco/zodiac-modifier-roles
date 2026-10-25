/**
 * Differential test: the SDK's `normalizeCondition` (packages/sdk/src/main/
 * condition/normalize) against its Lean transcription `Normalize.normalize`
 * (packages/evm/formal/Normalize), through the Lean driver's `nz` query.
 *
 * Random condition trees, built so that every normalization step has work to
 * do: Or/And over variants of one tree that differ in a single position
 * (pushDownOr), nested and single-child logical nodes, duplicates, trailing
 * Pass nodes and CallWithinAllowance children in calldata, Tuple and
 * AbiEncoded nodes of different widths (padding), leading bytes, and the
 * operators with effects (allowances, Custom, Pluck, Zip). A small pool of
 * compValues makes equal subtrees frequent. The TypeScript must not throw
 * on any of them.
 *
 * The second test checks the hypothesis of the normalization proof on
 * calldata: when `checkStored` accepts the normalized tree, the tree as
 * written is well-typed (`Bridge.invB`, the `iv` query).
 *
 * Needs the Lean driver: `cd formal && lake build roles-model`. Skipped when it
 * is missing. `SDK_NORMALIZE_CASES` sets the number of trees (default 3000),
 * `SDK_NORMALIZE_SEED` the seed, `SDK_NORMALIZE_SHOW_THROWS=1` prints why the
 * TypeScript threw.
 */
import { expect } from "chai";
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { normalizeCondition } from "../../../sdk/src/main/condition/normalize/index.js";
import { flattenCondition } from "../../../sdk/src/main/condition/flattenCondition.js";
import { checkStoredConditions } from "../../../sdk/src/main/condition/checkStored.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const LEAN_BIN = path.resolve(here, "../../formal/.lake/build/bin/roles-model");
const CASES = Number(process.env.SDK_NORMALIZE_CASES ?? 3000);
const SEED = Number(process.env.SDK_NORMALIZE_SEED ?? 1);

function mulberry32(seed: number) {
  return () => {
    seed |= 0;
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const rand = mulberry32(SEED);
const int = (n: number) => Math.floor(rand() * n);
const chance = (p: number) => rand() < p;
const pick = <T>(xs: readonly T[]): T => xs[int(xs.length)];

const E = { None: 0, Static: 1, Dynamic: 2, Tuple: 3, Array: 4, Abi: 5, Ether: 6 };
const O = {
  Pass: 0,
  And: 1,
  Or: 2,
  Matches: 5,
  ArraySome: 6,
  ArrayEvery: 7,
  ZipSome: 10,
  ZipEvery: 11,
  Slice: 13,
  Pluck: 14,
  EqualTo: 16,
  GreaterThan: 17,
  LessThan: 18,
  Custom: 22,
  WithinRatio: 23,
  WithinAllowance: 28,
  CallWithinAllowance: 30,
};

type C = {
  paramType: number;
  operator: number;
  compValue?: string;
  children?: C[];
};

const word = (n: number) => "0x" + n.toString(16).padStart(64, "0");
const node = (paramType: number, operator: number, compValue?: string, children?: C[]): C => ({
  paramType,
  operator,
  ...(compValue !== undefined && { compValue }),
  ...(children && { children }),
});

/** Parameter shapes. */
type Shape =
  | { k: "s" }
  | { k: "d" }
  | { k: "t"; fs: Shape[] }
  | { k: "a"; el: Shape }
  | { k: "c"; fs: Shape[] };

function genShape(depth: number): Shape {
  if (depth <= 0 || chance(0.45)) return chance(0.75) ? { k: "s" } : { k: "d" };
  const r = int(3);
  const fields = () => Array.from({ length: 1 + int(3) }, () => genShape(depth - 1));
  if (r === 0) return { k: "t", fs: fields() };
  if (r === 1) return { k: "a", el: genShape(depth - 1) };
  return { k: "c", fs: fields() };
}

const encOf = (s: Shape) =>
  s.k === "s" ? E.Static : s.k === "d" ? E.Dynamic : s.k === "t" ? E.Tuple : s.k === "a" ? E.Array : E.Abi;

/** A Pass describing the shape. */
function passOf(s: Shape): C {
  if (s.k === "t" || s.k === "c") return node(encOf(s), O.Pass, undefined, s.fs.map(passOf));
  if (s.k === "a") return node(E.Array, O.Pass, undefined, [passOf(s.el)]);
  return node(encOf(s), O.Pass);
}

/** Non-structural children: they read no parameter. */
function genNonStruct(): C {
  const r = int(5);
  if (r === 0) return node(E.None, O.CallWithinAllowance, word(1 + int(2)));
  if (r === 1) return node(E.Ether, O.LessThan, word(pick([10, 20])));
  if (r === 2) return node(E.None, O.WithinRatio, "0x0001" + "00".repeat(int(2)));
  if (r === 3) return node(E.Ether, O.WithinAllowance, word(1 + int(2)));
  return node(E.None, O.ZipEvery, "0x0001", [
    node(E.Tuple, O.Matches, undefined, [node(E.Static, O.Pass), node(E.Static, O.EqualTo, word(1))]),
  ]);
}

function genLeaf(s: Shape): C {
  if (s.k === "s") {
    const r = int(9);
    if (r <= 1) return node(E.Static, O.Pass);
    if (r <= 4) return node(E.Static, O.EqualTo, word(1 + int(3)));
    if (r === 5) return node(E.Static, O.LessThan, word(pick([100, 200])));
    if (r === 6) return node(E.Static, O.WithinAllowance, word(1 + int(2)));
    if (r === 7) return node(E.Static, O.Custom, "0x" + "cc".repeat(20) + pick(["", "01"]));
    if (chance(0.5)) return sliceOf(E.Static);
    return node(E.Static, O.Pluck, "0x0" + int(3));
  }
  if (s.k === "d") {
    const r = int(5);
    if (r === 0) return node(E.Dynamic, O.Pass);
    if (r === 4) return sliceOf(E.Dynamic);
    return node(E.Dynamic, O.EqualTo, pick(["0xaa", "0xaa0050bb", "0xbb", "0x"]));
  }
  return passOf(s);
}

const sliceOf = (paramType: number): C =>
  node(paramType, O.Slice, pick(["0x000001", "0x000420"]), [
    node(E.Static, pick([O.Pass, O.EqualTo]), word(int(2))),
  ]);

/** A shape close to `s`: a tuple or call with one field more or less. */
function nearShape(s: Shape): Shape {
  if (s.k === "t" || s.k === "c") {
    const fs = [...s.fs];
    if (fs.length > 1 && chance(0.5)) fs.pop();
    else if (chance(0.5)) fs.push(genShape(1));
    else {
      const i = int(fs.length);
      fs[i] = nearShape(fs[i]);
    }
    return { ...s, fs };
  }
  if (s.k === "a") return { k: "a", el: nearShape(s.el) };
  return s.k === "d" && chance(0.5) ? { k: "c", fs: [genShape(1)] } : s;
}

function gen(s: Shape, depth: number): C {
  if (depth <= 0) return genLeaf(s);
  const r = rand();
  if (r < 0.25) return genLogical(s, depth);
  if (s.k === "t" || s.k === "c") {
    if (r < 0.35) return node(encOf(s), O.Pass, undefined, s.fs.map(passOf));
    const children = s.fs.map((f) => gen(f, depth - 1));
    // trailing Pass nodes and non-structural children
    if (chance(0.3)) {
      for (let j = int(children.length); j < children.length; j++) children[j] = passOf(s.fs[j]);
    }
    if (chance(0.25)) children.splice(int(children.length + 1), 0, genNonStruct());
    // narrower than the shape: trailing fields left out
    const width = chance(0.2) ? 1 + int(children.length) : children.length;
    const cv =
      s.k === "c" && chance(0.4) ? pick(["0x0004aaaaaaaa", "0x0004bbbbbbbb", "0x0000"]) : undefined;
    return node(encOf(s), O.Matches, cv, children.slice(0, width));
  }
  if (s.k === "a") {
    const op = pick([O.ArraySome, O.ArrayEvery, O.Pass, O.Matches]);
    if (op === O.Pass) return passOf(s);
    if (op === O.Matches) {
      // element-wise, elements of slightly different shapes (variants)
      const k = 1 + int(3);
      return node(E.Array, O.Matches, undefined,
        Array.from({ length: k }, () => gen(chance(0.6) ? s.el : nearShape(s.el), depth - 1)));
    }
    return node(E.Array, op, undefined, [gen(s.el, depth - 1)]);
  }
  return genLeaf(s);
}

/** And/Or over the shape, often variants of one tree differing in one position. */
function genLogical(s: Shape, depth: number): C {
  const op = chance(0.6) ? O.Or : O.And;
  const n = 1 + int(3);
  let kids: C[];
  if (chance(0.5)) {
    const base = gen(s, depth - 1);
    kids = [base];
    for (let i = 1; i < n; i++) kids.push(variant(base, s, depth - 1));
  } else if (chance(0.3)) {
    // branches for different types: call variants, or misfitting tuples
    kids = Array.from({ length: n }, () => gen(chance(0.5) ? s : nearShape(s), depth - 1));
  } else {
    kids = Array.from({ length: n }, () => gen(s, depth - 1));
  }
  // branches of different widths (padding)
  if (chance(0.35)) {
    const i = int(kids.length);
    const k = kids[i];
    if (k.operator === O.Matches && k.children && k.children.length > 1) {
      kids[i] = { ...k, children: k.children.slice(0, 1 + int(k.children.length - 1)) };
    }
  }
  // a first child that reads no parameter (layout of the logical node)
  if (chance(0.12)) kids.unshift(node(E.Ether, O.LessThan, word(pick([10, 20]))));
  if (chance(0.15)) kids.push(kids[int(kids.length)]); // duplicate
  if (chance(0.15)) kids = [node(E.None, op, undefined, kids.slice(0, 2)), ...kids.slice(2)]; // nested
  return node(E.None, op, undefined, kids);
}

/** `base` with one child regenerated (or the whole node, if it has none). */
function variant(base: C, s: Shape, depth: number): C {
  const kids = base.children;
  if (!kids || kids.length === 0 || base.operator === O.Pass) return gen(s, depth);
  const i = int(kids.length);
  let fieldShape: Shape | undefined;
  if (base.operator === O.Matches && (s.k === "t" || s.k === "c")) {
    // position i reads field i only when no non-structural child precedes it
    fieldShape = s.fs[i];
  } else if (base.operator === O.And || base.operator === O.Or) {
    fieldShape = s;
  }
  const replacement = fieldShape && chance(0.85) ? gen(fieldShape, depth) : genLeaf(fieldShape ?? { k: "s" });
  return { ...base, children: kids.map((k, j) => (j === i ? replacement : k)) };
}

function genRoot(): C {
  const shape: Shape = { k: "c", fs: Array.from({ length: 1 + int(3) }, () => genShape(2)) };
  const depth = 1 + int(4);
  const root = gen(shape, depth);
  if (chance(0.15)) {
    const kids = root.children ?? [];
    return { ...root, children: [...kids, node(E.Static, O.Pass), node(E.Static, O.Pass)] };
  }
  return root;
}

const hex = (s?: string) => (s ?? "0x").slice(2).toLowerCase();
const flat = (c: C) =>
  flattenCondition(c as any)
    .map((n) => `${n.parent}:${n.paramType}:${n.operator}:${hex(n.compValue)}`)
    .join("|");

describe("SDK normalizeCondition vs Lean Normalize.normalize", function () {
  before(function () {
    if (!existsSync(LEAN_BIN)) this.skip();
  });

  it(`agrees on ${CASES} random condition trees`, function () {
    this.timeout(600_000);
    const cases: { input: string; ts: string }[] = [];
    let threw = 0;
    let changed = 0;
    const stats = { grew: 0, fewerOr: 0, fewerAnd: 0, reordered: 0 };
    for (let i = 0; i < CASES; i++) {
      const tree = genRoot();
      const input = flat(tree);
      let ts: string;
      try {
        ts = flat(normalizeCondition(structuredClone(tree) as any) as any);
      } catch (e) {
        if (process.env.SDK_NORMALIZE_SHOW_THROWS && threw < 2)
          console.log(`      threw: ${(e as Error).message}\n      on ${input}`);
        threw++;
        continue;
      }
      if (ts !== input) changed++;
      const count = (f: string, re: RegExp) => f.split("|").filter((n) => re.test(n)).length;
      const nIn = input.split("|").length;
      const nOut = ts.split("|").length;
      if (nOut > nIn) stats.grew++;
      if (count(ts, /^\d+:0:2:/) < count(input, /^\d+:0:2:/) && count(input, /^\d+:0:2:/) > 0) stats.fewerOr++;
      if (count(ts, /^\d+:0:1:/) < count(input, /^\d+:0:1:/)) stats.fewerAnd++;
      if (nOut === nIn && ts !== input) stats.reordered++;
      cases.push({ input, ts });
    }
    const res = spawnSync(LEAN_BIN, {
      input: cases.map((c) => `nz ${c.input}`).join("\n") + "\n",
      maxBuffer: 1 << 28,
    });
    expect(res.status, String(res.stderr)).to.equal(0);
    const out = String(res.stdout).trim().split("\n");
    expect(out.length).to.equal(cases.length);
    const diffs = cases
      .map((c, i) => ({ ...c, lean: out[i] }))
      .filter((c) => c.lean !== c.ts);
    console.log(
      `      ${cases.length} compared (${changed} changed by normalization), ${threw} skipped (TypeScript threw), ${diffs.length} differences`
    );
    console.log(`      ${JSON.stringify(stats)}`);
    for (const d of diffs.slice(0, 5)) {
      console.log(`      input ${d.input}\n      ts    ${d.ts}\n      lean  ${d.lean}`);
    }
    expect(diffs.length).to.equal(0);
    // normalizeCondition does not throw on these trees; a change that makes
    // it throw would otherwise go unnoticed (those trees are skipped)
    expect(threw, "normalizeCondition threw").to.equal(0);
  });

  it(`trees whose normalized form the SDK check accepts are well-typed`, function () {
    this.timeout(600_000);
    const qs: { input: string; norm: string }[] = [];
    let total = 0;
    let origRejected = 0;
    for (let i = 0; i < CASES; i++) {
      const tree = genRoot();
      const normalized = normalizeCondition(structuredClone(tree) as any) as any;
      total++;
      if (checkStoredConditions(flattenCondition(normalized) as any, true) === undefined) continue;
      if (checkStoredConditions(flattenCondition(tree as any) as any, true) === undefined) origRejected++;
      qs.push({ input: flat(tree), norm: flat(normalized) });
    }
    const res = spawnSync(LEAN_BIN, {
      input: qs.flatMap((q) => [`iv ${q.input}`, `iv ${q.norm}`]).join("\n") + "\n",
      maxBuffer: 1 << 28,
    });
    expect(res.status, String(res.stderr)).to.equal(0);
    const out = String(res.stdout).trim().split("\n");
    expect(out.length).to.equal(2 * qs.length);
    const badIn = qs.map((q, i) => ({ ...q, r: out[2 * i] })).filter((q) => q.r !== "ok");
    const badNorm = qs.map((q, i) => ({ ...q, r: out[2 * i + 1] })).filter((q) => q.r !== "ok");
    const why = new Map<string, number>();
    for (const b of badIn) why.set(b.r.split(" ")[2], (why.get(b.r.split(" ")[2]) ?? 0) + 1);
    console.log(
      `      ${qs.length} of ${total} accepted after normalization; not well-typed: ${badIn.length} as written, ${badNorm.length} normalized; the check rejects ${origRejected} of them as written`
    );
    for (const [k, n] of [...why].sort()) console.log(`      as written, ${k}: ${n}`);
    for (const b of badIn.slice(0, 4)) console.log(`      ${b.r} on ${b.input}`);
    for (const b of badNorm.slice(0, 2)) console.log(`      normalized ${b.r} on ${b.norm}`);
    expect(badNorm.length).to.equal(0);
    expect(badIn.length).to.equal(0);
  });
});
