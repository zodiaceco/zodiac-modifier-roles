/**
 * Integrity-gap fuzzer: condition trees that `Integrity.enforce` accepts but
 * that `evaluate` does not read the way their author meant.
 *
 * Each case starts from an intended ABI signature and a random value. It
 * builds a condition tree for that signature (compValues often match the
 * value, so a misread usually flips the result), then sometimes adds shapes
 * that Integrity accepts but that sit outside the decoder proof's
 * hypotheses (non-positional nodes inside containers, a Zip among `Matches`
 * children, ...). Every added shape leaves a tag.
 *
 * Trees Integrity rejects are skipped. For the others, a reference evaluator
 * written from the intended meaning (below, `ref`) gives ok / fail / unknown,
 * and `MockEvaluator` (Integrity → pack → unpack → evaluate) gives a status.
 * A mismatch is a bypass (reference fails, chain passes) or a false reject.
 * Mismatches are grouped by tag set; packages/sdk/INTEGRITY_BACKLOG.md
 * tracks the confirmed ones.
 *
 * Off by default. `GAP_CASES=2000 npx hardhat test test/formal/integrity-gaps.spec.ts`.
 * `GAP_CLEAN=1` adds only shapes inside the proof's hypotheses: any mismatch
 * then points at the reference evaluator (or a decoder bug). `GAP_SEED` sets
 * the PRNG seed, `GAP_REPORT=<file>` writes all mismatches as JSON.
 *
 * `GAP_CHECK=1` also runs the SDK check (`ConditionCheck.checkCondition` in
 * packages/evm/formal, via the Lean driver; build it with
 * `cd formal && lake build roles-model`). Every tree the check accepts is
 * evaluated without Integrity (as the `...Packed` setters store it) and must
 * match the reference; that is the only assertion in this mode. It also
 * reports which tagged shapes the check rejects that Integrity accepts, and
 * the reverse. `GAP_MUTATE=0.5` (with `GAP_CHECK=1`) also changes one node of
 * that share of trees (operator, encoding, compValue length or a boundary
 * byte) to probe the operator rules; mutated trees are only compared on
 * accept/reject.
 */
import { expect } from "chai";
import {
  AbiCoder,
  ContractFactory,
  getBytes,
  hexlify,
  keccak256,
  toBeHex,
  zeroPadValue,
} from "ethers";
import { spawnSync } from "node:child_process";
import { writeFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import hre, { network } from "hardhat";

import { Encoding, Operator, flattenCondition } from "../utils.js";

const CASES = Number(process.env.GAP_CASES ?? 0);
const SEED = Number(process.env.GAP_SEED ?? 1);
const CLEAN = process.env.GAP_CLEAN === "1";
const REPORT = process.env.GAP_REPORT;
const CHECK = process.env.GAP_CHECK === "1";
const MUTATE = Number(process.env.GAP_MUTATE ?? 0);
const LEAN_BIN = path.resolve(
  path.dirname(fileURLToPath(import.meta.url)),
  "../../formal/.lake/build/bin/roles-model",
);

const OPS = [
  0, 1, 2, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
  28, 30,
];

/** A `WithinRatio` compValue: slots, decimals, ratios, optional adapters. */
function ratioCv(): Uint8Array {
  const pick = <T>(xs: T[]) => xs[int(xs.length)];
  const head = [
    int(4),
    pick([0, 18, 27, 28]),
    int(4),
    pick([0, 6, 27, 28]),
    ...bytes(4).map((b) => (chance(0.3) ? 0 : b)),
    ...bytes(4).map((b) => (chance(0.3) ? 0 : b)),
  ];
  const blob = () => {
    const n = pick([0, 0, 5, 20, 24]);
    return [n, ...bytes(n)];
  };
  const tail = chance(0.5) ? [] : chance(0.5) ? blob() : [...blob(), ...blob()];
  const out = [...head, ...tail];
  if (chance(0.2)) out.pop();
  return Uint8Array.from(out);
}

/** Changes one node of a flat tree; returns a description. */
function mutate(flat: any[]): string {
  const i = int(flat.length);
  const n = flat[i];
  const was = Operator[n.operator];
  const leaf = !flat.some((m, j) => j > 0 && m.parent === i);
  switch (int(leaf ? 5 : 4)) {
    case 0:
      n.operator = OPS[int(OPS.length)];
      return `op ${was}→${Operator[n.operator]}`;
    case 1:
      n.paramType = int(7);
      return `enc→${Encoding[n.paramType]} on ${was}`;
    case 2: {
      const len = [0, 1, 2, 3, 4, 5, 12, 20, 31, 32, 33, 34, 54, 63, 64, 65][
        int(16)
      ];
      n.compValue = hexlify(bytes(len));
      return `cv length ${len} on ${was}`;
    }
    case 3: {
      const b = getBytes(n.compValue);
      if (b.length === 0) return `cv byte (empty) on ${was}`;
      const k = int(Math.min(b.length, 4));
      b[k] = [0, 1, 27, 28, 32, 33, 254, 255][int(8)];
      n.compValue = hexlify(b);
      return `cv byte ${k} on ${was}`;
    }
    default: {
      const op = [
        Operator.WithinRatio,
        Operator.WithinAllowance,
        Operator.CallWithinAllowance,
        Operator.Custom,
        Operator.Empty,
      ][int(5)];
      n.operator = op;
      if (op === Operator.WithinRatio) {
        n.paramType = Encoding.None;
        n.compValue = hexlify(ratioCv());
      } else if (op === Operator.WithinAllowance) {
        n.compValue = hexlify(bytes([32, 34, 54, 53][int(4)]));
      } else if (op === Operator.CallWithinAllowance) {
        n.paramType = Encoding.None;
        n.compValue = hexlify(bytes(32));
      } else if (op === Operator.Custom) {
        n.compValue = hexlify(bytes([19, 20, 52][int(3)]));
      } else {
        n.paramType = Encoding.None;
        n.compValue = "0x";
      }
      return `leaf→${Operator[op]}`;
    }
  }
}

/** `checkStored true` on each flat tree, via the Lean driver. */
function leanCheck(flats: any[][]): boolean[] {
  const lines = flats.map(
    (flat) =>
      "ck 1 " +
      flat
        .map(
          (n) =>
            `${n.parent}:${n.paramType}:${n.operator}:${String(n.compValue).slice(2)}`,
        )
        .join("|"),
  );
  const res = spawnSync(LEAN_BIN, {
    input: lines.join("\n") + "\n",
    maxBuffer: 1 << 28,
  });
  if (res.status !== 0) throw new Error(String(res.stderr));
  const out = String(res.stdout).trim().split("\n");
  if (out.length !== lines.length) throw new Error("lean: short output");
  return out.map((o) => o === "ok" || o === "ns");
}

function errName(e: any, iface: any): string {
  let parsed: string | undefined;
  try {
    parsed = iface.parseError(e?.data)?.name;
  } catch {}
  return (
    e?.revert?.name ??
    parsed ??
    (/OutOfGas/.test(JSON.stringify(e?.data ?? e?.message ?? ""))
      ? "out of gas"
      : undefined) ??
    String(e?.shortMessage ?? e?.message ?? e).slice(0, 60)
  );
}

const abi = AbiCoder.defaultAbiCoder();

// ---------------------------------------------------------------------------
// Randomness
// ---------------------------------------------------------------------------

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
const pick = <T>(xs: T[]): T => xs[int(xs.length)];
const bytes = (n: number) => Uint8Array.from({ length: n }, () => int(256));
const cat = (...bs: Uint8Array[]) => Uint8Array.from(bs.flatMap((b) => [...b]));
const eqBytes = (a: Uint8Array, b: Uint8Array) =>
  a.length === b.length && a.every((x, i) => x === b[i]);

/** Anomaly tags of the current case. */
let tags: Set<string>;
const tag = (t: string) => {
  tags.add(t);
};

// ---------------------------------------------------------------------------
// Intended ABI types and values
// ---------------------------------------------------------------------------

type WordAbi = "uint256" | "int256" | "address" | "bytes32" | "bool";
/** Leading bytes of nested calldata: `n` bytes, checked against `prefix`. */
type Lead = { n: number; checked: boolean; prefix: Uint8Array };
type Ty =
  | { k: "word"; abi: WordAbi }
  | { k: "bytes" }
  | { k: "tuple"; cs: Ty[] }
  | { k: "array"; e: Ty }
  | { k: "call"; args: Ty[]; lead: Lead }
  /** a `bytes` value with several interpretations (bytes or calls) */
  | { k: "variant"; alts: Ty[] };

type CallVal = { prefix: Uint8Array; args: any[] };
type VariantVal = { alt: number; v: any };

function randLead(): Lead {
  if (chance(0.7)) return { n: 4, checked: chance(0.3), prefix: bytes(4) };
  const n = int(7);
  return { n, checked: chance(0.5), prefix: bytes(n) };
}

function randTy(depth: number, variants = true): Ty {
  const r = int(depth <= 0 ? 2 : variants ? 6 : 5);
  if (r === 0)
    return {
      k: "word",
      abi: pick(["uint256", "int256", "address", "bytes32", "bool"]),
    };
  if (r === 1) return { k: "bytes" };
  if (r === 2)
    return {
      k: "tuple",
      cs: Array.from({ length: 1 + int(3) }, () => randTy(depth - 1, variants)),
    };
  if (r === 3) return { k: "array", e: randTy(depth - 1, variants) };
  if (r === 4) return randCall(depth - 1, variants);
  const call = () => randCall(depth - 1, variants);
  return {
    k: "variant",
    alts: chance(0.5) ? [{ k: "bytes" }, call()] : [call(), call()],
  };
}

const randCall = (depth: number, variants = true): Ty => ({
  k: "call",
  args: Array.from({ length: 1 + int(3) }, () => randTy(depth, variants)),
  lead: randLead(),
});

function abiType(t: Ty): string {
  switch (t.k) {
    case "word":
      return t.abi;
    case "tuple":
      return `(${t.cs.map(abiType).join(",")})`;
    case "array":
      return `${abiType(t.e)}[]`;
    default:
      return "bytes";
  }
}

function randVal(t: Ty): any {
  switch (t.k) {
    case "word":
      if (t.abi === "address") return hexlify(bytes(20));
      if (t.abi === "bool") return chance(0.5);
      if (t.abi === "bytes32") return hexlify(bytes(32));
      if (t.abi === "int256")
        return BigInt.asIntN(256, BigInt(hexlify(bytes(32))));
      return chance(0.3) ? BigInt(int(1000)) : BigInt(hexlify(bytes(32)));
    case "bytes":
      return hexlify(bytes(int(70)));
    case "tuple":
      return t.cs.map(randVal);
    case "array":
      return Array.from({ length: int(4) }, () => randVal(t.e));
    case "call": {
      const prefix =
        t.lead.checked && chance(0.75) ? t.lead.prefix : bytes(t.lead.n);
      return { prefix, args: t.args.map(randVal) } as CallVal;
    }
    case "variant": {
      const alt = int(t.alts.length);
      return { alt, v: randVal(t.alts[alt]) } as VariantVal;
    }
  }
}

/** The value as ethers encodes it. */
function toEth(t: Ty, v: any): any {
  switch (t.k) {
    case "tuple":
      return t.cs.map((c, i) => toEth(c, v[i]));
    case "array":
      return v.map((x: any) => toEth(t.e, x));
    case "call":
    case "variant":
      return hexlify(raw(t, v));
    default:
      return v;
  }
}

/** Content bytes of a bytes-like value (bytes, nested calldata). */
function raw(t: Ty, v: any): Uint8Array {
  if (t.k === "bytes") return getBytes(v);
  if (t.k === "call") {
    const c = v as CallVal;
    return cat(
      c.prefix,
      getBytes(
        abi.encode(
          t.args.map(abiType),
          t.args.map((a, i) => toEth(a, c.args[i])),
        ),
      ),
    );
  }
  if (t.k === "variant") {
    const x = v as VariantVal;
    return raw(t.alts[x.alt], x.v);
  }
  throw new Error("not bytes-like");
}

const isStatic = (t: Ty): boolean =>
  t.k === "word" || (t.k === "tuple" && t.cs.every(isStatic));

/** The bytes of the value at its location: inline encoding for static
 *  types, the tail block (length/count word included) for dynamic ones. */
function encodeAt(t: Ty, v: any): Uint8Array {
  const enc = getBytes(abi.encode([abiType(t)], [toEth(t, v)]));
  return isStatic(t) ? enc : enc.slice(32);
}

/** What `Slice` and `Bitmask` index into. */
function content(t: Ty, v: any): Uint8Array {
  return t.k === "word" ? encodeAt(t, v) : raw(t, v);
}

// ---------------------------------------------------------------------------
// Condition trees
// ---------------------------------------------------------------------------

type Node = {
  paramType: Encoding;
  operator: Operator;
  compValue?: string;
  children?: Node[];
  /** non-positional: evaluated in place, consumes no parameter */
  np?: boolean;
  /** which variant alternative an AbiEncoded node interprets */
  alt?: number;
};

const word = (b: Uint8Array) => zeroPadValue(b, 32);
/** EqualTo compValue as `abi.encode(value)` gives it: dynamic values carry
 *  a leading offset word, which the packer strips again. */
const eqCv = (t: Ty, v: any) => abi.encode([abiType(t)], [toEth(t, v)]);
const u16 = (n: number) => Uint8Array.from([(n >> 8) & 0xff, n & 0xff]);
const randWord = () => hexlify(bytes(32));

/** Pass conditions that only describe the type (all structural). */
function passFor(t: Ty): Node {
  switch (t.k) {
    case "word":
      return { paramType: Encoding.Static, operator: Operator.Pass };
    case "bytes":
    case "variant":
      return { paramType: Encoding.Dynamic, operator: Operator.Pass };
    case "tuple":
      return {
        paramType: Encoding.Tuple,
        operator: Operator.Pass,
        children: t.cs.map(passFor),
      };
    case "array":
      return {
        paramType: Encoding.Array,
        operator: Operator.Pass,
        children: [passFor(t.e)],
      };
    case "call":
      return {
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        compValue: leadCv(t.lead),
        children: t.args.map(passFor),
      };
  }
}

function leadCv(l: Lead): string {
  if (l.checked) return hexlify(cat(u16(l.n), l.prefix));
  if (l.n === 4 && chance(0.5)) return "0x";
  return hexlify(u16(l.n));
}

function bitmaskNode(paramType: Encoding, bs: Uint8Array): Node {
  const shift = chance(0.85) && bs.length > 0 ? int(bs.length) : int(80);
  const n = 1 + int(chance(0.8) ? Math.max(1, bs.length - shift) : 40);
  const mask = bytes(n);
  const expected = Uint8Array.from(mask, (m, j) =>
    shift + j < bs.length ? bs[shift + j] & m : int(256),
  );
  if (chance(0.4)) expected[int(n)] ^= 1 << int(8);
  return {
    paramType,
    operator: Operator.Bitmask,
    compValue: hexlify(cat(u16(shift), mask, expected)),
  };
}

function compareNode(paramType: Encoding, w: Uint8Array): Node {
  const r = int(5);
  if (r <= 1)
    return {
      paramType,
      operator: Operator.EqualTo,
      compValue: chance(0.6) ? word(w) : randWord(),
    };
  const near = BigInt(hexlify(word(w))) + BigInt(int(3)) - 1n;
  return {
    paramType,
    operator: pick([
      Operator.GreaterThan,
      Operator.LessThan,
      Operator.SignedIntGreaterThan,
      Operator.SignedIntLessThan,
    ]),
    compValue: chance(0.6)
      ? toBeHex(BigInt.asUintN(256, near), 32)
      : randWord(),
  };
}

function sliceNode(paramType: Encoding, bs: Uint8Array): Node {
  const shift = chance(0.85) && bs.length > 0 ? int(bs.length) : int(80);
  const size =
    chance(0.85) && bs.length > shift
      ? 1 + int(Math.min(32, bs.length - shift))
      : 1 + int(32);
  const window = bs.slice(shift, shift + size);
  const r = int(4);
  const child: Node =
    r === 0
      ? { paramType: Encoding.Static, operator: Operator.Pass }
      : r === 1
        ? bitmaskNode(Encoding.Static, window)
        : compareNode(Encoding.Static, window);
  return {
    paramType,
    operator: Operator.Slice,
    compValue: hexlify(cat(u16(shift), Uint8Array.from([size]))),
    children: [child],
  };
}

/** A non-positional node: an EtherValue check, Empty, or a logical node of
 *  those. Never a Zip (Zips are placed by `withZip`). */
function genNP(depth = 1): Node {
  const r = int(10);
  if (r < 7) {
    const op = pick([
      Operator.Pass,
      Operator.EqualTo,
      Operator.EqualTo,
      Operator.GreaterThan,
      Operator.LessThan,
    ]);
    const cv =
      op === Operator.Pass
        ? undefined
        : chance(0.5)
          ? word(Uint8Array.from([0]))
          : word(Uint8Array.from([int(3)]));
    return {
      paramType: Encoding.EtherValue,
      operator: op,
      compValue: cv,
      np: true,
    };
  }
  if (r < 8 || depth <= 0)
    return { paramType: Encoding.None, operator: Operator.Empty, np: true };
  return {
    paramType: Encoding.None,
    operator: chance(0.5) ? Operator.And : Operator.Or,
    children: [genNP(depth - 1), genNP(depth - 1)],
    np: true,
  };
}

/** Inserts non-positional nodes among `kids` (an anomaly unless `legit`). */
function injectNP(kids: Node[], where: string, legit: boolean): Node[] {
  if (!(legit ? chance(0.35) : !CLEAN && chance(0.2))) return kids;
  const out = [...kids];
  const pos = int(out.length + 1);
  out.splice(pos, 0, genNP());
  if (!legit) tag(`np-in-${where}${pos === 0 ? "-first" : ""}`);
  return out;
}

const opName = (op: Operator) => Operator[op];

/** A positional condition for a value `v` of type `t`. */
function gen(t: Ty, v: any, depth = 0): Node {
  let n = genBase(t, v, depth);
  if (chance(0.12) && depth < 4) {
    // And/Or of two conditions on the same value, maybe with EtherValue
    // checks beside them (legit: logical nodes evaluate every child in place).
    const op = chance(0.5) ? Operator.And : Operator.Or;
    const kids = injectNP([n, genBase(t, v, depth + 1)], "logic", true);
    n = { paramType: Encoding.None, operator: op, children: kids };
  }
  return n;
}

function genBase(t: Ty, v: any, depth: number): Node {
  switch (t.k) {
    case "word": {
      const w = encodeAt(t, v);
      const r = int(10);
      if (r < 2) return { paramType: Encoding.Static, operator: Operator.Pass };
      if (r < 6) return compareNode(Encoding.Static, w);
      if (r < 7) return bitmaskNode(Encoding.Static, w);
      if (r < 9) {
        tag("slice");
        return sliceNode(Encoding.Static, w);
      }
      return { paramType: Encoding.Static, operator: Operator.Pass };
    }
    case "bytes": {
      const bs = raw(t, v);
      const r = int(10);
      if (r < 3)
        return { paramType: Encoding.Dynamic, operator: Operator.Pass };
      if (r < 6) {
        const enc = encodeAt(t, v);
        return {
          paramType: Encoding.Dynamic,
          operator: Operator.EqualTo,
          compValue: chance(0.6)
            ? eqCv(t, v)
            : hexlify(bytes(64 + 32 * int(3))),
        };
      }
      if (r < 8) return bitmaskNode(Encoding.Dynamic, bs);
      tag("slice");
      return sliceNode(Encoding.Dynamic, bs);
    }
    case "tuple": {
      const op = pick([
        Operator.Matches,
        Operator.Matches,
        Operator.Pass,
        Operator.EqualTo,
      ]);
      let kids = t.cs.map((c, i) => gen(c, v[i], depth + 1));
      kids = injectNP(kids, `${opName(op)}-tuple`, false);
      const n: Node = {
        paramType: Encoding.Tuple,
        operator: op,
        children: kids,
      };
      if (op === Operator.EqualTo) {
        const enc = getBytes(eqCv(t, v));
        n.compValue = chance(0.6)
          ? hexlify(enc)
          : hexlify(bytes(Math.max(64, enc.length)));
      }
      return n;
    }
    case "array": {
      const op = pick([
        Operator.Pass,
        Operator.ArraySome,
        Operator.ArrayEvery,
        Operator.ArrayTailMatches,
        Operator.EqualTo,
        Operator.Matches,
      ]);
      const xs = v as any[];
      let kids: Node[];
      if (op === Operator.Matches) {
        // element-wise: exactly one condition per element
        tag("matches-array");
        const k = chance(0.8) ? Math.max(1, xs.length) : 1 + int(3);
        kids = Array.from({ length: k }, (_, j) =>
          gen(t.e, j < xs.length ? xs[j] : randVal(t.e), depth + 1),
        );
      } else if (op === Operator.ArrayTailMatches) {
        const k = 1 + int(2);
        kids = Array.from({ length: k }, (_, j) => {
          const x = xs[xs.length - k + j];
          return gen(t.e, x === undefined ? randVal(t.e) : x, depth + 1);
        });
      } else {
        kids = [gen(t.e, xs.length ? pick(xs) : randVal(t.e), depth + 1)];
      }
      if (op === Operator.Pass || op === Operator.EqualTo)
        kids = injectNP(kids, `${opName(op)}-array`, false);
      const n: Node = {
        paramType: Encoding.Array,
        operator: op,
        children: kids,
      };
      if (op === Operator.EqualTo)
        n.compValue = chance(0.6) ? eqCv(t, v) : hexlify(bytes(64));
      return n;
    }
    case "call": {
      const c = v as CallVal;
      let kids = t.args.map((a, i) => gen(a, c.args[i], depth + 1));
      kids = injectNP(kids, "Matches-call", false);
      return {
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        compValue: leadCv(t.lead),
        children: kids,
      };
    }
    case "variant": {
      tag("variant");
      const x = v as VariantVal;
      const kids = t.alts.map((a, j) => {
        const val = j === x.alt ? x.v : randVal(a);
        const n = gen(a, val, depth + 1);
        if (a.k === "call") n.alt = j;
        return n;
      });
      if (chance(0.5)) kids.reverse();
      return {
        paramType: Encoding.None,
        operator: chance(0.7) ? Operator.Or : Operator.And,
        children: kids,
      };
    }
  }
}

// ---------------------------------------------------------------------------
// Root, Plucks and Zips
// ---------------------------------------------------------------------------

type Case = { t: Ty; v: any; root: Node };

function genCase(): Case {
  tags = new Set();
  if (chance(0.08)) {
    // calldata with several interpretations
    tag("root-variant");
    const t: Ty = {
      k: "variant",
      alts: [randCall(1), randCall(1)],
    };
    const v = randVal(t);
    return { t, v, root: gen(t, v) };
  }
  // Shallow trees: Integrity's gas grows ~3x per nesting level.
  const t = randCall(chance(0.6) ? 1 : 2) as Extract<Ty, { k: "call" }>;
  if (chance(0.3)) t.lead = { n: 4, checked: false, prefix: bytes(4) };
  let v = randVal(t) as CallVal;
  let root: Node;
  if (chance(0.35)) {
    ({ root, v } = withZip(t, v));
  } else {
    root = gen(t, v);
  }
  if (chance(0.15)) {
    tag("root-logic");
    root = {
      paramType: Encoding.None,
      operator: chance(0.5) ? Operator.And : Operator.Or,
      children: injectNP([root], "root", true),
    };
  }
  return { t, v, root };
}

/** Adds 2-3 array parameters, plucks them and zips them. */
function withZip(
  t: Extract<Ty, { k: "call" }>,
  v: CallVal,
): { root: Node; v: CallVal } {
  const F = 2 + int(2);
  const len = int(4);
  const elems = Array.from({ length: F }, () => randTy(1, false));
  const arrays = elems.map((e) =>
    Array.from({ length: chance(0.15) ? int(4) : len }, () => randVal(e)),
  );
  // insert the arrays as parameters
  const positions: number[] = [];
  for (let f = 0; f < F; f++) {
    const p = int(t.args.length + 1);
    t.args.splice(p, 0, { k: "array", e: elems[f] });
    v.args.splice(p, 0, arrays[f]);
    for (let j = 0; j < positions.length; j++)
      if (positions[j] >= p) positions[j]++;
    positions.push(p);
  }
  const slots = Array.from({ length: F }, (_, f) => f * 3 + int(3));
  const kids: Node[] = t.args.map((a, i) => {
    const f = positions.indexOf(i);
    if (f < 0) return gen(a, v.args[i], 1);
    return {
      paramType: Encoding.Array,
      operator: Operator.Pluck,
      compValue: hexlify(Uint8Array.from([slots[f]])),
      children: [passFor(elems[f])],
    };
  });
  const zip: Node = {
    paramType: Encoding.None,
    operator: chance(0.5) ? Operator.ZipEvery : Operator.ZipSome,
    compValue: hexlify(Uint8Array.from(slots)),
    children: [
      {
        paramType: Encoding.Tuple,
        operator: Operator.Matches,
        children: elems.map((e, f) =>
          gen(e, arrays[f].length ? pick(arrays[f]) : randVal(e), 1),
        ),
      },
    ],
    np: true,
  };
  const call: Node = {
    paramType: Encoding.AbiEncoded,
    operator: Operator.Matches,
    compValue: leadCv(t.lead),
    children: kids,
  };
  const last = Math.max(...positions);
  const r = CLEAN ? 0 : int(5);
  if (r === 4) {
    // anywhere inside a later parameter's condition
    const spots: Node[] = [];
    const walk = (n: Node) => {
      if (n.children?.length && n.operator !== Operator.Slice) spots.push(n);
      n.children?.forEach(walk);
    };
    kids.slice(last + 1).forEach(walk);
    if (spots.length) {
      const host = pick(spots);
      const p = int(host.children!.length + 1);
      host.children!.splice(p, 0, zip);
      tag(
        `zip-in-${opName(host.operator)}-${Encoding[host.paramType]}${p === 0 ? "-first" : p === host.children!.length - 1 ? "-last" : "-mid"}`,
      );
      return { root: call, v };
    }
  }
  if (r === 0 || (r >= 2 && last === kids.length - 1)) {
    tag("zip");
    return {
      root: {
        paramType: Encoding.None,
        operator: Operator.And,
        children: [call, zip],
      },
      v,
    };
  }
  if (r === 1) {
    const p = last + 1 + int(kids.length - last);
    kids.splice(p, 0, zip);
    tag(p === kids.length - 1 ? "zip-in-matches-last" : "zip-in-matches-mid");
    return { root: call, v };
  }
  // And[param, Zip] or And[Zip, param] for a later parameter
  const i = last + 1 + int(kids.length - last - 1);
  const first = chance(0.5);
  tag(first ? "zip-first-in-param-and" : "zip-after-param-in-and");
  kids[i] = {
    paramType: Encoding.None,
    operator: Operator.And,
    children: first ? [zip, kids[i]] : [kids[i], zip],
  };
  return { root: call, v };
}

// ---------------------------------------------------------------------------
// Reference evaluator: the intended meaning
// ---------------------------------------------------------------------------

type R = "ok" | "fail" | "unk";
type Slot = { t: Ty; v: any };
type Cx = { slots: Map<number, Slot> };

function and(rs: (() => R)[]): R {
  let res: R = "ok";
  for (const r of rs) {
    const x = r();
    if (x === "fail") return "fail";
    if (x === "unk") res = "unk";
  }
  return res;
}
function or(rs: (() => R)[]): R {
  let res: R = "fail";
  for (const r of rs) {
    const x = r();
    if (x === "ok") return "ok";
    if (x === "unk") res = "unk";
  }
  return res;
}

const cvValue = (cv: string): bigint => {
  const b = getBytes(cv);
  return BigInt(
    b.length > 32
      ? keccak256(b)
      : hexlify(cat(b, new Uint8Array(32 - b.length))),
  );
};
const asWord = (b: Uint8Array): bigint =>
  b.length > 32 ? BigInt(keccak256(b)) : BigInt(hexlify(word(b)));
const signed = (x: bigint) => BigInt.asIntN(256, x);

function compare(op: Operator, value: bigint, cv: string): R {
  const c = cvValue(cv);
  let ok: boolean;
  if (op === Operator.EqualTo) ok = value === c;
  else if (op === Operator.GreaterThan) ok = value > c;
  else if (op === Operator.LessThan) ok = value < c;
  else if (op === Operator.SignedIntGreaterThan) ok = signed(value) > signed(c);
  else if (op === Operator.SignedIntLessThan) ok = signed(value) < signed(c);
  else throw new Error(`compare ${op}`);
  return ok ? "ok" : "fail";
}

function bitmask(bs: Uint8Array, cv: string): R {
  const b = getBytes(cv);
  const shift = (b[0] << 8) | b[1];
  const n = (b.length - 2) / 2;
  if (shift + n > bs.length) return "fail";
  for (let j = 0; j < n; j++)
    if ((bs[shift + j] & b[2 + j]) !== b[2 + n + j]) return "fail";
  return "ok";
}

function isCompare(op: Operator) {
  return op >= Operator.EqualTo && op <= Operator.SignedIntLessThan;
}

function refNP(n: Node, cx: Cx): R {
  switch (n.operator) {
    case Operator.Pass:
      return "ok";
    case Operator.Empty:
      return "fail";
    case Operator.And:
      return and(n.children!.map((c) => () => refNP(c, cx)));
    case Operator.Or:
      return or(n.children!.map((c) => () => refNP(c, cx)));
    case Operator.ZipSome:
    case Operator.ZipEvery: {
      const cv = getBytes(n.compValue!);
      const arrays = [...cv].map((s) => cx.slots.get(s));
      if (arrays.some((a) => !a)) throw new Error("zip before pluck");
      const len = (arrays[0]!.v as any[]).length;
      if (arrays.some((a) => (a!.v as any[]).length !== len)) return "fail";
      const fields = n.children![0].children!;
      const tupleAt = (i: number) => () =>
        and(
          fields.map((fld, f) => () => {
            const a = arrays[f]!;
            const t = a.t as Extract<Ty, { k: "array" }>;
            return ref(fld, t.e, (a.v as any[])[i], cx);
          }),
        );
      const tuples = Array.from({ length: len }, (_, i) => tupleAt(i));
      return n.operator === Operator.ZipEvery ? and(tuples) : or(tuples);
    }
    default:
      if (n.paramType === Encoding.EtherValue && isCompare(n.operator))
        return compare(n.operator, 0n, n.compValue!);
      throw new Error(`refNP ${opName(n.operator)}`);
  }
}

/** Children of a container: positional ones take the next field. */
function seq(kids: Node[], ts: Ty[], vs: any[], cx: Cx): R {
  let p = 0;
  const steps = kids.map((c) => {
    if (c.np) return () => refNP(c, cx);
    const i = p++;
    return () => ref(c, ts[i], vs[i], cx);
  });
  if (p !== ts.length) throw new Error("generator: positional count");
  return and(steps);
}

function ref(n: Node, t: Ty, v: any, cx: Cx): R {
  if (n.np) return refNP(n, cx);
  const op = n.operator;
  if (op === Operator.And)
    return and(n.children!.map((c) => () => ref(c, t, v, cx)));
  if (op === Operator.Or)
    return or(n.children!.map((c) => () => ref(c, t, v, cx)));

  if (t.k === "variant") {
    const x = v as VariantVal;
    if (n.paramType === Encoding.AbiEncoded)
      return n.alt === x.alt ? ref(n, t.alts[x.alt], x.v, cx) : "unk";
    // a bytes-level check on the raw content
    return ref(n, { k: "bytes" }, hexlify(raw(t, v)), cx);
  }

  switch (op) {
    case Operator.Pass:
      return "ok";
    case Operator.Matches: {
      if (t.k === "tuple") return seq(n.children!, t.cs, v, cx);
      if (t.k === "array") {
        const xs = v as any[];
        if (n.children!.filter((c) => !c.np).length !== xs.length)
          return "fail";
        return seq(
          n.children!,
          xs.map(() => t.e),
          xs,
          cx,
        );
      }
      if (t.k !== "call") throw new Error("Matches on " + t.k);
      const c = v as CallVal;
      if (t.lead.checked && !eqBytes(c.prefix, t.lead.prefix)) return "fail";
      return seq(n.children!, t.args, c.args, cx);
    }
    case Operator.ArraySome:
    case Operator.ArrayEvery: {
      if (t.k !== "array") throw new Error("array op");
      const steps = (v as any[]).map(
        (x) => () =>
          and(
            n.children!.map(
              (c) => () => (c.np ? refNP(c, cx) : ref(c, t.e, x, cx)),
            ),
          ),
      );
      return op === Operator.ArrayEvery ? and(steps) : or(steps);
    }
    case Operator.ArrayTailMatches: {
      if (t.k !== "array") throw new Error("array op");
      const xs = v as any[];
      const k = n.children!.filter((c) => !c.np).length;
      if (xs.length < k) return "fail";
      let j = 0;
      return and(
        n.children!.map((c) => {
          if (c.np) return () => refNP(c, cx);
          const x = xs[xs.length - k + j++];
          return () => ref(c, t.e, x, cx);
        }),
      );
    }
    case Operator.Bitmask:
      return bitmask(content(t, v), n.compValue!);
    case Operator.Slice: {
      const bs = content(t, v);
      const cv = getBytes(n.compValue!);
      const shift = (cv[0] << 8) | cv[1];
      const size = cv[2];
      if (shift + size > bs.length) return "fail";
      return refSliced(n.children![0], bs.slice(shift, shift + size));
    }
    case Operator.Pluck:
      cx.slots.set(getBytes(n.compValue!)[0], { t, v });
      return "ok";
    default:
      if (isCompare(op)) {
        const cv =
          op === Operator.EqualTo && !isStatic(t)
            ? "0x" + n.compValue!.slice(2 + 64)
            : n.compValue!;
        return compare(op, asWord(encodeAt(t, v)), cv);
      }
      throw new Error(`ref ${opName(op)}`);
  }
}

function refSliced(n: Node, window: Uint8Array): R {
  if (n.operator === Operator.Pass) return "ok";
  if (n.operator === Operator.Bitmask) return bitmask(window, n.compValue!);
  return compare(n.operator, BigInt(hexlify(word(window))), n.compValue!);
}

// ---------------------------------------------------------------------------
// Test
// ---------------------------------------------------------------------------

/** Deep copy without the generator's annotations. */
const strip = (n: Node): any => ({
  paramType: n.paramType,
  operator: n.operator,
  compValue: n.compValue,
  children: n.children?.map(strip),
});

function show(n: Node): string {
  const enc = Encoding[n.paramType];
  const cv =
    n.compValue && n.compValue !== "0x"
      ? `(${n.compValue.length > 14 ? n.compValue.slice(0, 12) + "…" : n.compValue})`
      : "";
  const kids = n.children?.length ? `[${n.children.map(show).join(", ")}]` : "";
  return `${opName(n.operator)}:${enc}${cv}${kids}`;
}

const depth = (n: Node): number =>
  1 + Math.max(0, ...(n.children ?? []).map(depth));
const count = (n: Node): number =>
  1 + (n.children ?? []).reduce((s, c) => s + count(c), 0);

function sig(t: Ty): string {
  if (t.k === "call") return `(${t.args.map(sig).join(",")})`;
  if (t.k === "variant") return `variant<${t.alts.map(sig).join("|")}>`;
  if (t.k === "tuple") return `(${t.cs.map(sig).join(",")})`;
  if (t.k === "array") return `${sig(t.e)}[]`;
  return t.k === "word" ? t.abi : "bytes";
}

describe("Integrity gaps (fuzz)", function () {
  this.timeout(0);

  it(`accepted trees evaluate as intended (${CASES} cases)`, async function () {
    if (CASES <= 0) this.skip();
    rand = mulberry32(SEED);

    let connection: Awaited<ReturnType<typeof network.create>> | undefined;
    let evaluator: any;
    const fresh = async () => {
      await connection?.close();
      connection = await network.create();
      const { ethers } = connection;
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
    };

    const rejected = new Map<string, number>();
    const tagStats = new Map<string, { accepted: number; rejected: number }>();
    let accepted = 0;
    let unknown = 0;
    let outOfGas = 0;
    let compared = 0;
    type Mismatch = {
      kind: "bypass" | "false-reject";
      tags: string;
      status: string;
      sig: string;
      tree: string;
      size: number;
      data: string;
      flat: any;
    };
    const mismatches: Mismatch[] = [];

    const cases = Array.from({ length: CASES }, () => {
      const cs = genCase();
      const flat = flattenCondition(strip(cs.root)).map((f) => ({ ...f }));
      let mutated: string | undefined;
      if (CHECK && MUTATE > 0 && chance(MUTATE)) mutated = mutate(flat);
      return {
        ...cs,
        tags: mutated ? new Set([...tags, `mut: ${mutated}`]) : new Set(tags),
        flat,
        mutated,
      };
    });
    const checked = CHECK ? leanCheck(cases.map((cs) => cs.flat)) : [];
    let checkAccepted = 0;
    let checkCompared = 0;
    const checkMismatches: Mismatch[] = [];
    const onlyIntegrity = new Map<string, number>();
    const onlyCheck = new Map<string, number>();
    const examples = new Map<string, string>();
    const bump = (m: Map<string, number>, k: string, flat?: any[]) => {
      m.set(k, (m.get(k) ?? 0) + 1);
      if (flat && !examples.has(k))
        examples.set(
          k,
          flat
            .map(
              (n, i) =>
                `${i}<${n.parent} ${Encoding[n.paramType]}:${Operator[n.operator]}:${String(n.compValue).slice(0, 20)}`,
            )
            .join(" "),
        );
    };

    for (let c = 0; c < CASES; c++) {
      if (c % 200 === 0) await fresh();
      const { t, v, root, flat } = cases[c];
      tags = cases[c].tags;
      const data = hexlify(raw(t, v));
      const tagKey = [...tags].sort().join(" ") || "(none)";

      if (checked[c] && !cases[c].mutated) {
        checkAccepted++;
        let okU: boolean;
        let statusU: string;
        try {
          const s = Number(
            await evaluator.evaluateUnchecked(data, flat, {
              gasLimit: 16_000_000,
            }),
          );
          okU = s === 0;
          statusU = okU ? "Ok" : `status ${s}`;
        } catch (e: any) {
          okU = false;
          statusU = `revert ${errName(e, evaluator.interface)}`;
        }
        const exp = ref(root, t, v, { slots: new Map() });
        if (exp !== "unk") {
          checkCompared++;
          if ((exp === "ok") !== okU)
            checkMismatches.push({
              kind: okU ? "bypass" : "false-reject",
              tags: tagKey,
              status: statusU,
              sig: sig(t),
              tree: show(root),
              size: count(root),
              data,
              flat: flat.map((f) => ({ ...f })),
            });
        }
      }

      let status: string;
      let ok: boolean;
      try {
        const s = Number(
          await evaluator.evaluate(data, flat, { gasLimit: 16_000_000 }),
        );
        status = s === 0 ? "Ok" : `status ${s}`;
        ok = s === 0;
      } catch (e: any) {
        const name = errName(e, evaluator.interface);
        if (name === "out of gas") {
          outOfGas++;
          if (process.env.GAP_DEBUG)
            console.log(
              `OOG size ${count(root)} depth ${depth(root)} sig ${sig(t)}`,
            );
          continue;
        }
        const integrity = /^[A-Z][A-Za-z]+$/.test(name) && name !== "Panic";
        if (integrity) {
          rejected.set(name, (rejected.get(name) ?? 0) + 1);
          if (checked[c]) bump(onlyCheck, `${name} | ${tagKey}`, flat);
          for (const tg of tags) {
            const st = tagStats.get(tg) ?? { accepted: 0, rejected: 0 };
            st.rejected++;
            tagStats.set(tg, st);
          }
          continue;
        }
        status = `revert ${name}`;
        ok = false;
      }
      accepted++;
      if (CHECK && !checked[c]) bump(onlyIntegrity, tagKey, flat);
      if (cases[c].mutated) continue;
      if (process.env.GAP_DEBUG)
        console.log(`OK  size ${count(root)} depth ${depth(root)}`);
      for (const tg of tags) {
        const st = tagStats.get(tg) ?? { accepted: 0, rejected: 0 };
        st.accepted++;
        tagStats.set(tg, st);
      }

      const expected = ref(root, t, v, { slots: new Map() });
      if (expected === "unk") {
        unknown++;
        continue;
      }
      compared++;
      if ((expected === "ok") === ok) continue;
      mismatches.push({
        kind: ok ? "bypass" : "false-reject",
        tags: tagKey,
        status,
        sig: sig(t),
        tree: show(root),
        size: count(root),
        data,
        flat: flat.map((f) => ({ ...f })),
      });
    }
    await connection?.close();

    console.log(
      `      ${CASES} cases: ${accepted} accepted by Integrity, ${compared} compared, ${unknown} unknown (stray variant), ${outOfGas} out of gas`,
    );
    for (const [why, n] of [...rejected].sort((a, b) => b[1] - a[1]))
      console.log(`      rejected ${n}× ${why}`);
    for (const [tg, st] of [...tagStats].sort())
      console.log(
        `      tag ${tg}: ${st.accepted} accepted, ${st.rejected} rejected`,
      );

    const groups = new Map<string, Mismatch[]>();
    for (const m of mismatches) {
      const k = `${m.kind} | ${m.tags}`;
      groups.set(k, [...(groups.get(k) ?? []), m]);
    }
    for (const [k, ms] of [...groups].sort(
      (a, b) => b[1].length - a[1].length,
    )) {
      const m = ms.reduce((a, b) => (b.size < a.size ? b : a));
      console.log(`\n      ${ms.length}× ${k}`);
      console.log(`        sig    ${m.sig}`);
      console.log(`        tree   ${m.tree}`);
      console.log(`        status ${m.status}`);
    }
    if (REPORT)
      writeFileSync(
        REPORT,
        JSON.stringify(
          mismatches,
          (_, x) => (typeof x === "bigint" ? x.toString() : x),
          2,
        ),
      );
    if (CHECK) {
      console.log(
        `\n      check: ${checkAccepted} accepted, ${checkCompared} compared without Integrity, ${checkMismatches.length} mismatches`,
      );
      for (const [k, n] of [...onlyIntegrity].sort((a, b) => b[1] - a[1]))
        console.log(`      Integrity accepts, check rejects ${n}× ${k}`);
      for (const [k, n] of [...onlyCheck].sort((a, b) => b[1] - a[1]))
        console.log(`      check accepts, Integrity rejects ${n}× ${k}`);
      if (process.env.GAP_EXAMPLES)
        for (const [k, e] of examples)
          console.log(`\n      EXAMPLE ${k}\n        ${e}`);
      for (const m of checkMismatches.slice(0, 5)) {
        console.log(`\n      CHECK MISMATCH ${m.kind} | ${m.tags}`);
        console.log(`        sig    ${m.sig}`);
        console.log(`        tree   ${m.tree}`);
        console.log(`        status ${m.status}`);
      }
      expect(checkMismatches.length).to.equal(0);
      return;
    }
    expect(mismatches.length).to.equal(0);
  });
});
