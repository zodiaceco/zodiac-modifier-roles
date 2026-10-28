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
 *
 * `GAP_NORMALIZE=1` also runs the SDK's `normalizeCondition` on every tree
 * Integrity accepts and evaluates the result on the same calldata. The
 * normalized tree must be accepted by Integrity and give the same verdict as
 * the input tree (and as the reference, where it knows the answer); that is
 * the only assertion in this mode. The value-level proof of normalization
 * (formal/Normalize) does not see calldata layout; this does.
 *
 * `GAP_EVAL=<n>` runs a separate test: `n` generated trees (with allowance
 * checks added) on generated calldata (corrupted in half the cases), with
 * random allowance balances and `msg.value`. For every tree Integrity
 * accepts, the Lean model of `evaluate` (formal/Evaluate, driver query `ev`)
 * must give the contract's exact status and consumptions
 * (`MockEvaluator.evaluateWith`).
 *
 * With `GAP_PACKED=1` the trees take the path the SDK uses: they are gated by
 * the SDK's `checkStored` instead of Integrity, packed by the SDK's
 * `packConditions` and evaluated from that buffer
 * (`MockEvaluator.evaluatePackedWith`), as the `...Packed` setters store it.
 * Trees the SDK check accepts and Integrity rejects are listed (and the
 * other way round counted). `GAP_GAS` sets the gas limit (default 16M).
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
import { existsSync, mkdtempSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

import hre, { network } from "hardhat";

import {
  checkStored,
  toFlatNodes,
  tyKey,
} from "../../../sdk/src/main/condition/checkStored.js";
import { normalizeCondition } from "../../../sdk/src/main/condition/normalize/index.js";
import {
  checkStoredConditions,
  toFlatNodes,
} from "../../../sdk/src/main/condition/checkStored.js";
import {
  checkAndPack,
  packConditions,
} from "../../../sdk/src/main/condition/packConditions.js";
import { Encoding, Operator, flattenCondition } from "../utils.js";

const CASES = Number(process.env.GAP_CASES ?? 0);
const SEED = Number(process.env.GAP_SEED ?? 1);
const TARGET = Number(process.env.GAP_TARGET ?? 0);
const CLEAN = process.env.GAP_CLEAN === "1" || TARGET > 0;
const REPORT = process.env.GAP_REPORT;
const CHECK = process.env.GAP_CHECK === "1";
const MUTATE = Number(process.env.GAP_MUTATE ?? 0);
const NORMALIZE = process.env.GAP_NORMALIZE === "1";
const EVAL = Number(process.env.GAP_EVAL ?? 0);
const PACKED = process.env.GAP_PACKED === "1";
const GAS = BigInt(process.env.GAP_GAS ?? 16_000_000);
/** Allowance keys used in `GAP_EVAL` mode. */
const KEYS = ["0x" + "a1".repeat(32), "0x" + "b2".repeat(32)];
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

/** `checkStored true` on each flat tree, via the Lean driver; also checks
 *  that the SDK's transcription gives the same verdict. */
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
  flats.forEach((flat, i) => {
    const v = checkStored(toFlatNodes(flat), true);
    const ts =
      v === undefined
        ? "none"
        : v.kind === "noCalldata"
          ? "ns"
          : `ok ${tyKey(v.type)}`;
    if (ts !== out[i])
      throw new Error(
        `SDK checkStored differs from Lean: ${lines[i]}\n  lean ${out[i]}\n  sdk  ${ts}`,
      );
  });
  return out.map((o) => o.startsWith("ok") || o === "ns");
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

type WordAbi =
  | "uint256"
  | "int256"
  | "address"
  | "bytes32"
  | "bool"
  // narrow types (GAP_TARGET only)
  | "uint8"
  | "uint64"
  | "int8"
  | "int64"
  | "bytes1"
  | "bytes4";
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
  if (NORMALIZE && chance(0.4)) {
    const a = call();
    return { k: "variant", alts: [a, nearCall(a)] };
  }
  return {
    k: "variant",
    alts: chance(0.5) ? [{ k: "bytes" }, call()] : [call(), call()],
  };
}

/** A call type close to `t`: one tuple gets a field more or less, or the
 *  last argument is dropped or one added (normalization pads such variants). */
function nearCall(t: Ty): Ty {
  const c = structuredClone(t) as Extract<Ty, { k: "call" }>;
  const tuples: Extract<Ty, { k: "tuple" }>[] = [];
  const walk = (x: Ty) => {
    if (x.k === "tuple") {
      tuples.push(x);
      x.cs.forEach(walk);
    }
    if (x.k === "array") walk(x.e);
  };
  c.args.forEach(walk);
  const r = int(3);
  if (r === 0 && tuples.length) {
    const tp = pick(tuples);
    if (tp.cs.length > 1 && chance(0.5)) tp.cs.pop();
    else tp.cs.push(randTy(0, false));
  } else if (r === 1 && c.args.length > 1) c.args.pop();
  else c.args.push(randTy(1, false));
  return c;
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
      if (t.abi === "uint8") return BigInt(int(256));
      if (t.abi === "uint64") return BigInt(hexlify(bytes(8)));
      if (t.abi === "int8") return BigInt.asIntN(8, BigInt(int(256)));
      if (t.abi === "int64")
        return BigInt.asIntN(64, BigInt(hexlify(bytes(8))));
      if (t.abi === "bytes1") return hexlify(bytes(1));
      if (t.abi === "bytes4") return hexlify(bytes(4));
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
  if ((EVAL || TARGET) && chance(0.3))
    return chance(0.5)
      ? {
          paramType: Encoding.None,
          operator: Operator.CallWithinAllowance,
          compValue: pick(KEYS),
          np: true,
        }
      : {
          paramType: Encoding.EtherValue,
          operator: Operator.WithinAllowance,
          compValue: pick(KEYS),
          np: true,
        };
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

/** The shape that exposes memory aliasing in the consumption list (in
 *  `GAP_EVAL` mode): charge `k`, then an `Or` whose first branch charges `k`
 *  again and fails, then (sometimes) charge `k` once more:
 *  `And[charge(k), Or[And[charge(k), fail], n], charge(k)?]`. If the failed
 *  branch's charge leaked into the shared entry or list, the reported
 *  consumption is too high, or the last charge is refused. Charges are per
 *  call (1 each, independent of the ether value); `fail` is an ether value
 *  below 0, which never holds. Placed by `gen`, so it also sits inside array
 *  element conditions (iterators roll back too) and nested `Or`s. */
function aliasWrap(n: Node): Node {
  tag("alias");
  const k = pick(KEYS);
  const charge = (): Node => ({
    paramType: Encoding.None,
    operator: Operator.CallWithinAllowance,
    compValue: k,
    np: true,
  });
  const fail: Node = {
    paramType: Encoding.EtherValue,
    operator: Operator.LessThan,
    compValue: word(Uint8Array.from([0])),
    np: true,
  };
  const failing: Node = {
    paramType: Encoding.None,
    operator: Operator.And,
    children: [charge(), fail],
    np: true,
  };
  return {
    paramType: Encoding.None,
    operator: Operator.And,
    children: [
      charge(),
      {
        paramType: Encoding.None,
        operator: Operator.Or,
        children: [failing, n],
      },
      ...(chance(0.5) ? [charge()] : []),
    ],
  };
}

/** A positional condition for a value `v` of type `t`. */
function gen(t: Ty, v: any, depth = 0): Node {
  let n = genBase(t, v, depth);
  if ((EVAL || TARGET) && chance(0.12) && depth < 4) return aliasWrap(n);
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
      if ((EVAL || TARGET) && chance(0.15))
        return {
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: pick(KEYS),
        };
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
  elemTy: () => Ty = () => randTy(1, false),
  F = 2 + int(2),
): { root: Node; v: CallVal } {
  const len = int(4);
  const elems = Array.from({ length: F }, elemTy);
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
  const at = TARGET ? int(Math.max(1, len)) : 0;
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
          gen(
            e,
            // GAP_TARGET: one row of the zipped arrays, so the tuple
            // condition holds for some row
            TARGET && at < arrays[f].length
              ? arrays[f][at]
              : arrays[f].length
                ? pick(arrays[f])
                : randVal(e),
            1,
          ),
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
      kind: string;
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
        suffix: chance(0.4) ? bytes(32 * (1 + int(3))) : undefined,
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
    const normThrows = new Map<string, number>();
    let normCompared = 0;
    const normMismatches: Mismatch[] = [];
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
      // trailing bytes are valid calldata; a misplaced read may land there
      const data = hexlify(
        cat(
          raw(t, v),
          NORMALIZE && cases[c].suffix ? cases[c].suffix : new Uint8Array(),
        ),
      );
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
      if (NORMALIZE) {
        const expN = ref(root, t, v, { slots: new Map() });
        let normalized: any;
        try {
          normalized = normalizeCondition(strip(root));
        } catch (e: any) {
          bump(normThrows, String(e.message ?? e).slice(0, 60));
        }
        // the SDK stores the normalized tree with a `...Packed` setter: it
        // must pass the SDK check (not Integrity) whenever the tree as
        // written does, and is evaluated without Integrity
        const checkedAsWritten = (() => {
          try {
            return checkStoredConditions(flat as any) !== undefined;
          } catch {
            return false;
          }
        })();
        if (normalized && checkedAsWritten) {
          normCompared++;
          const nflat = flattenCondition(normalized).map((f) => ({ ...f }));
          let nStatus: string;
          let nOk = false;
          let integrityN = false;
          let nChecked = false;
          try {
            nChecked = checkStoredConditions(nflat as any) !== undefined;
          } catch {
            nChecked = false;
          }
          if (!nChecked) {
            integrityN = true;
            nStatus = "rejected by the SDK check";
          } else {
            try {
              const s = Number(
                await evaluator.evaluateUnchecked(data, nflat, {
                  gasLimit: 16_000_000,
                }),
              );
              nOk = s === 0;
              nStatus = nOk ? "Ok" : `status ${s}`;
            } catch (e: any) {
              nStatus = `revert ${errName(e, evaluator.interface)}`;
            }
          }
          if (
            integrityN ||
            nOk !== ok ||
            (expN !== "unk" && (expN === "ok") !== nOk)
          )
            normMismatches.push({
              kind: integrityN
                ? "normalized-rejected"
                : nOk && !ok
                  ? "normalize-widens"
                  : nOk !== ok
                    ? "normalize-narrows"
                    : "normalize-vs-ref",
              tags: tagKey,
              status: `${status} -> ${nStatus} (ref ${expN})`,
              sig: sig(t),
              tree: `${show(root)}\n        normd  ${show(normalized)}`,
              size: count(root),
              data,
              flat: nflat,
            });
        }
      }
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
      `      ${CASES} cases: ${accepted} accepted by Integrity, ${compared} compared, ${unknown} unknown (malformed calldata below a trailing Pass, which the reference does not judge), ${outOfGas} out of gas`,
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
    if (NORMALIZE) {
      console.log(
        `\n      normalize: ${normCompared} normalized and evaluated, ${normMismatches.length} mismatches`,
      );
      for (const [k, n] of [...normThrows].sort((a, b) => b[1] - a[1]))
        console.log(`      SDK threw ${n}× ${k}`);
      const ng = new Map<string, Mismatch[]>();
      for (const m of normMismatches) {
        const k = `${m.kind} | ${m.tags}`;
        ng.set(k, [...(ng.get(k) ?? []), m]);
      }
      for (const [k, ms] of [...ng].sort((a, b) => b[1].length - a[1].length)) {
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
            normMismatches,
            (_, x) => (typeof x === "bigint" ? x.toString() : x),
            2,
          ),
        );
      // normalization keeps every child, so the verdict never changes
      expect(normMismatches.length).to.equal(0);
      return;
    }
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

  it(`the Lean model of evaluate agrees with the contract (${EVAL} cases)`, async function () {
    if (EVAL <= 0) this.skip();
    rand = mulberry32(SEED);
    let connection: Awaited<ReturnType<typeof network.create>> | undefined;
    let evaluator: any;
    const fresh = async () => {
      await connection?.close();
      connection = await network.create({
        override: { blockGasLimit: GAS > 30_000_000n ? GAS : 30_000_000n },
      } as any);
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
    /** Flips, cuts or extends the calldata. */
    const corrupt = (data: Uint8Array): Uint8Array => {
      const d = Uint8Array.from(data);
      const r = int(4);
      if (r === 0 && d.length) d[int(d.length)] ^= 1 << int(8);
      else if (r === 1 && d.length) {
        // a length or offset word: make it large or off by one word
        const at = 4 + 32 * int(Math.max(1, (d.length - 4) >> 5));
        if (at + 32 <= d.length)
          d[at + 31 - int(2)] ^= pick([0x20, 0x01, 0x80]);
        return d;
      } else if (r === 2) return d.slice(0, int(d.length + 1));
      else return cat(d, bytes(32 * int(3)));
      return d;
    };
    const hexNo0x = (h: string) => h.slice(2).toLowerCase();

    type Q = {
      line: string;
      data: string;
      flat: any[];
      value: number;
      bal: bigint[];
      alias: boolean;
    };
    const queries: Q[] = [];
    for (let c = 0; c < EVAL; c++) {
      const { t, v, root } = genCase();
      const alias = tags.has("alias");
      let data = raw(t, v);
      if (chance(0.5)) data = corrupt(data);
      const flat = flattenCondition(strip(root)).map((f) => ({ ...f }));
      const value = pick([0, 1, 2, 500]);
      const bal = KEYS.map(() => pick([0n, 1n, 2n, 1000n, 2n ** 128n - 1n]));
      const nodes = flat
        .map(
          (f) =>
            `${f.parent}:${f.paramType}:${f.operator}:${hexNo0x(f.compValue ?? "0x")}`,
        )
        .join("|");
      const allowances = KEYS.map((k, i) => `${hexNo0x(k)}:${bal[i]}`).join(
        ",",
      );
      queries.push({
        line: `ev ${value} ${allowances} ${hexlify(data)} ${nodes}`,
        data: hexlify(data),
        flat,
        value,
        bal,
        alias,
      });
    }
    // The contract first: cases that run out of gas (a corrupted array
    // length makes AbiLocation loop) are not sent to the model.
    let rejected = 0;
    let oog = 0;
    // PACKED: trees the SDK check and Integrity disagree on
    let sdkStricter = 0;
    const sdkLooser = new Map<string, { n: number; example: string }>();
    const looserLines: string[] = [];
    const stricterLines: string[] = [];
    const chain: (string | undefined)[] = [];
    for (let c = 0; c < queries.length; c++) {
      if (c % 200 === 0) await fresh();
      const q = queries[c];
      let packed: string | undefined;
      if (PACKED) {
        let intErr: string | undefined;
        try {
          await evaluator.enforceIntegrity.staticCall(q.flat, {
            gasLimit: GAS,
          });
        } catch (e: any) {
          intErr = errName(e, evaluator.interface);
        }
        let verdict;
        try {
          verdict = checkStoredConditions(q.flat);
        } catch {
          verdict = undefined;
        }
        if (verdict === undefined) {
          rejected++;
          if (intErr === undefined) {
            sdkStricter++;
            stricterLines.push(q.line.split(" ").pop()!);
          }
          chain.push(undefined);
          continue;
        }
        if (intErr !== undefined) {
          looserLines.push(`${intErr} ${q.line.split(" ").pop()}`);
          const e = sdkLooser.get(intErr) ?? {
            n: 0,
            example: q.line.split(" ").pop()!,
          };
          e.n++;
          sdkLooser.set(intErr, e);
        }
        packed = hexlify(packConditions(toFlatNodes(q.flat)));
      }
      try {
        const [status, cons] = PACKED
          ? await evaluator.evaluatePackedWith.staticCall(
              q.data,
              packed,
              q.value,
              KEYS,
              q.bal,
              { gasLimit: GAS },
            )
          : await evaluator.evaluateWith.staticCall(
              q.data,
              q.flat,
              q.value,
              KEYS,
              q.bal,
              { gasLimit: GAS },
            );
        const cs = (cons as any[]).map(
          (x) => `${hexNo0x(x.allowanceKey)}:${x.balance}:${x.consumed}`,
        );
        chain.push(`${Number(status)} ${cs.length ? cs.join(",") : "-"}`);
      } catch (e: any) {
        const name = errName(e, evaluator.interface);
        if (name === "out of gas") {
          oog++;
          chain.push(undefined);
        } else if (
          !PACKED &&
          /^[A-Z][A-Za-z]+$/.test(name) &&
          name !== "Panic"
        ) {
          rejected++;
          chain.push(undefined);
        } else chain.push("255 -");
      }
    }
    const asked = queries.filter((_, c) => chain[c] !== undefined);
    if (REPORT && PACKED) {
      writeFileSync(REPORT + ".looser", looserLines.join("\n") + "\n");
      writeFileSync(REPORT + ".stricter", stricterLines.join("\n") + "\n");
    }
    if (REPORT) {
      writeFileSync(REPORT, asked.map((q) => q.line).join("\n") + "\n");
      writeFileSync(
        REPORT + ".chain",
        chain.filter((x) => x !== undefined).join("\n") + "\n",
      );
    }
    const res = spawnSync(LEAN_BIN, {
      input: asked.map((q) => q.line).join("\n") + "\n",
      maxBuffer: 1 << 28,
    });
    expect(res.status, String(res.stderr)).to.equal(0);
    const lean = String(res.stdout).trim().split("\n");
    expect(lean.length).to.equal(asked.length);

    const statuses = new Map<string, number>();
    const diffs: string[] = [];
    const answers = chain.filter((x): x is string => x !== undefined);
    const compared = answers.length;
    answers.forEach((ch, k) => {
      const st = ch.split(" ")[0];
      statuses.set(st, (statuses.get(st) ?? 0) + 1);
      if (ch !== lean[k])
        diffs.push(
          `chain ${ch}\n        lean  ${lean[k]}\n        ${asked[k].line.slice(0, 600)}`,
        );
    });
    await connection?.close();
    const aliasCompared = asked.filter((q) => q.alias).length;
    const aliasOk = asked.filter(
      (q, k) => q.alias && answers[k].startsWith("0 "),
    ).length;
    console.log(
      `      aliasing shape: ${aliasCompared} compared, ${aliasOk} passed`,
    );
    console.log(
      `      ${EVAL} cases${PACKED ? " (packed path)" : ""}: ${compared} compared, ${rejected} rejected by ${PACKED ? "the SDK check" : "Integrity"}, ${oog} out of gas, ${diffs.length} differences`,
    );
    if (PACKED) {
      const looser = [...sdkLooser.values()].reduce((a, e) => a + e.n, 0);
      console.log(
        `      SDK check accepts, Integrity rejects: ${looser}; Integrity accepts, SDK check rejects: ${sdkStricter}`,
      );
      for (const [name, e] of [...sdkLooser].sort((a, b) => b[1].n - a[1].n))
        console.log(`        ${e.n}× ${name}  e.g. ${e.example.slice(0, 300)}`);
    }
    console.log(
      `      statuses ${[...statuses]
        .sort((a, b) => Number(a[0]) - Number(b[0]))
        .map(([k, n]) => `${k}:${n}`)
        .join(" ")}`,
    );
    for (const d of diffs.slice(0, 8)) console.log(`      ${d}`);
    expect(diffs.length).to.equal(0);
  });
  /* -------------------------------------------------------------------------
   * GAP_TARGET: does the target decode what Roles checked?
   *
   * Roles reads calldata with its own walker; the target with solc's ABI
   * decoder. For random signatures (words, bytes, tuples, arrays, nested
   * calldata), valid but non-canonical encodings (tails reordered, gapped
   * or shared, dirty padding, trailing junk, offsets into the head,
   * sometimes dirty narrow words; nested calldata laid out loosely too) and
   * random conditions (with Plucks and Zips, or Plucks and WithinRatio, in
   * some), Roles evaluates the crafted calldata, a solc-compiled target
   * decodes it (`calldata` and `memory` parameters) and returns
   * `abi.encode` of what it decoded. Nested calldata goes to a second echo
   * function (its receiver), whose result replaces it. Roles evaluates
   * that canonical calldata too. A call Roles passes and the target accepts
   * must pass canonically with the same consumptions, or those of another
   * choice of passing `Or` branches: otherwise Roles let through values it
   * rejects when they are encoded plainly. Trees take the SDK path (gated
   * by `checkAndPack`, evaluated packed), not Integrity.
   * ---------------------------------------------------------------------- */
  it(`the target decodes what Roles checked (${TARGET} cases)`, async function () {
    if (TARGET <= 0) this.skip();
    const SOLC =
      process.env.GAP_SOLC ??
      path.join(
        os.homedir(),
        "Library/Caches/hardhat-nodejs/compilers-v3/macosx-amd64/solc-macosx-amd64-v0.8.37+commit.f401782d",
      );
    if (!existsSync(SOLC)) this.skip();
    rand = mulberry32(SEED);

    // types: words, bytes, tuples, arrays, nested calldata (a `bytes`
    // parameter holding a call, which a second target decodes)
    const tTy = (depth: number): Ty => {
      const r = int(depth <= 0 ? 2 : 5);
      if (r === 4)
        return {
          k: "call",
          args: Array.from({ length: 1 + int(2) }, () => tTy(depth - 1)),
          lead: { n: 4, checked: chance(0.3), prefix: bytes(4) },
        };
      if (r === 0)
        return {
          k: "word",
          abi: pick([
            "uint256",
            "int256",
            "address",
            "bytes32",
            "bool",
            "uint8",
            "uint64",
            "int8",
            "int64",
            "bytes1",
            "bytes4",
          ] as WordAbi[]),
        };
      if (r === 1) return { k: "bytes" };
      if (r === 2)
        return {
          k: "tuple",
          cs: Array.from({ length: 1 + int(3) }, () => tTy(depth - 1)),
        };
      return { k: "array", e: tTy(depth - 1) };
    };

    // ---------------------------------------------------- loose encoder
    const DIRTY = 0.03;
    const w32 = (n: bigint) => getBytes(toBeHex(BigInt.asUintN(256, n), 32));
    const junk = (words: number) => bytes(32 * words);
    const wordEnc = (t: Extract<Ty, { k: "word" }>, v: any): Uint8Array => {
      switch (t.abi) {
        case "uint256":
          return w32(v);
        case "int256":
          return w32(v);
        case "uint8":
        case "uint64": {
          const bits = t.abi === "uint8" ? 8 : 64;
          return w32(
            chance(DIRTY) ? v | (1n << BigInt(bits + int(256 - bits))) : v,
          );
        }
        case "int8":
        case "int64": {
          const bits = t.abi === "int8" ? 8 : 64;
          const x = BigInt.asUintN(256, v);
          return w32(
            chance(DIRTY) ? x ^ (1n << BigInt(bits + int(256 - bits))) : x,
          );
        }
        case "bytes1":
        case "bytes4": {
          const n = t.abi === "bytes1" ? 1 : 4;
          const b = new Uint8Array(32);
          b.set(getBytes(v), 0);
          if (chance(DIRTY)) b[n + int(32 - n)] = 1 + int(255);
          return b;
        }
        case "bytes32":
          return getBytes(v);
        case "address": {
          const b = getBytes(zeroPadValue(v, 32));
          if (chance(DIRTY)) b[int(12)] = 1 + int(255);
          return b;
        }
        case "bool":
          return w32(chance(DIRTY) ? BigInt(2 + int(5)) : v ? 1n : 0n);
      }
    };
    const staticEnc = (t: Ty, v: any): Uint8Array =>
      t.k === "word"
        ? wordEnc(t, v)
        : cat(...(t as any).cs.map((c: Ty, i: number) => staticEnc(c, v[i])));
    const tailEnc = (t: Ty, v: any): Uint8Array => {
      if (t.k === "bytes" || t.k === "call") {
        // nested calldata: its own arguments laid out loosely too
        const c =
          t.k === "bytes"
            ? getBytes(v)
            : chance(0.15)
              ? raw(t, v)
              : cat(v.prefix, block(t.args, v.args));
        const pad = (32 - (c.length % 32)) % 32;
        const padding = chance(0.2) ? bytes(pad) : new Uint8Array(pad);
        return cat(
          w32(BigInt(c.length)),
          c,
          padding,
          chance(0.15) ? junk(1) : new Uint8Array(0),
        );
      }
      if (t.k === "array")
        return cat(
          w32(BigInt(v.length)),
          block(
            v.map(() => t.e),
            v,
          ),
        );
      if (t.k === "tuple") return block(t.cs, v);
      throw new Error("not dynamic");
    };
    const headSize = (t: Ty): number =>
      isStatic(t)
        ? t.k === "word"
          ? 32
          : (t as any).cs.reduce((a: number, c: Ty) => a + headSize(c), 0)
        : 32;
    function block(ts: Ty[], vs: any[]): Uint8Array {
      const headLen = ts.reduce((a, t) => a + headSize(t), 0);
      const dyn = ts.map((t, i) => i).filter((i) => !isStatic(ts[i]));
      if (chance(0.4)) dyn.sort(() => rand() - 0.5);
      let cursor = headLen;
      const tails: Uint8Array[] = [];
      if (chance(0.2)) {
        const g = junk(1 + int(2));
        tails.push(g);
        cursor += g.length;
      }
      const offsets = new Map<number, number>();
      const placed: { enc: string; at: number }[] = [];
      for (const i of dyn) {
        const enc = tailEnc(ts[i], vs[i]);
        const same = placed.find((p) => p.enc === hexlify(enc));
        if (same && chance(0.5)) {
          offsets.set(i, same.at);
          continue;
        }
        if (chance(0.03) && headLen > 0) {
          offsets.set(i, 32 * int(headLen / 32));
          continue;
        }
        offsets.set(i, cursor);
        placed.push({ enc: hexlify(enc), at: cursor });
        tails.push(enc);
        cursor += enc.length;
        if (chance(0.2)) {
          const g = junk(1 + int(2));
          tails.push(g);
          cursor += g.length;
        }
      }
      const head = ts.map((t, i) =>
        isStatic(t) ? staticEnc(t, vs[i]) : w32(BigInt(offsets.get(i)!)),
      );
      return cat(...head, ...tails);
    }

    // ---------------------------------------------------- echo targets
    const structs = new Map<string, string>();
    const solT = (t: Ty): string => {
      if (t.k === "word") return t.abi;
      if (t.k === "bytes" || t.k === "call") return "bytes";
      if (t.k === "array") return solT(t.e) + "[]";
      if (t.k === "tuple") {
        const key = abiType(t);
        if (!structs.has(key)) {
          const name = `S${structs.size}`;
          structs.set(key, name);
          structs.set(
            name,
            `struct ${name} { ${t.cs.map((c, i) => `${solT(c)} f${i};`).join(" ")} }`,
          );
        }
        return structs.get(key)!;
      }
      throw new Error("unsupported");
    };
    const needsLoc = (t: Ty) => t.k !== "word";
    /** echo functions per contract (keeps each under the code size limit) */
    const CHUNK = 50;

    type TCase = {
      t: Extract<Ty, { k: "call" }>;
      v: CallVal;
      root: Node;
      flat: any[];
      args: Uint8Array;
      value: number;
      bal: bigint[];
      /** what the tree exercises beyond per-node checks */
      feats: string[];
      /** packed by the SDK, undefined if its check rejects the tree */
      packed?: string;
    };
    // The SDK path (what zodiac-os stores through the `...Packed` setters):
    // the SDK check gates the tree, Roles evaluates the packed buffer.
    const pack = (flat: any[]): string | undefined => {
      try {
        return checkAndPack(flat).packed;
      } catch {
        return undefined;
      }
    };
    const cases: TCase[] = [];
    const hasCall = (t: Ty): boolean =>
      t.k === "call" ||
      (t.k === "tuple" && t.cs.some(hasCall)) ||
      (t.k === "array" && hasCall(t.e));
    const NUMERIC = ["uint256", "uint8", "uint64"];

    /** `And[call, (Pluck ether value)?, WithinRatio]`: two plucked values
     *  (numeric parameters, or one of them the ether value), a ratio window
     *  around their actual ratio, so some calls pass and some do not. */
    const withRatio = (
      t: Extract<Ty, { k: "call" }>,
      v: CallVal,
      value: number,
    ): Node | undefined => {
      const nums = t.args
        .map((a, i) => i)
        .filter(
          (i) =>
            t.args[i].k === "word" && NUMERIC.includes((t.args[i] as any).abi),
        );
      const ether = chance(0.3);
      while (nums.length < (ether ? 1 : 2)) {
        // add a numeric parameter, or turn one into one (legacy codegen
        // runs out of stack slots beyond 3 parameters)
        const a: Ty = { k: "word", abi: pick(NUMERIC) as WordAbi };
        const others = t.args.map((_, i) => i).filter((i) => !nums.includes(i));
        if (t.args.length >= 3) {
          const p = pick(others);
          t.args[p] = a;
          v.args[p] = randVal(a);
          nums.push(p);
          continue;
        }
        const p = int(t.args.length + 1);
        t.args.splice(p, 0, a);
        v.args.splice(p, 0, randVal(a));
        for (let j = 0; j < nums.length; j++) if (nums[j] >= p) nums[j]++;
        nums.push(p);
      }
      nums.sort(() => rand() - 0.5);
      const ps = nums.slice(0, ether ? 1 : 2);
      // mostly small amounts: scaled by up to 10^18, large ones overflow
      for (const p of ps)
        if (chance(0.7)) {
          const abi = (t.args[p] as any).abi;
          v.args[p] = BigInt(int(abi === "uint8" ? 256 : 1_000_000));
        }
      const slots = [int(3), 3 + int(3)];
      const amount = (j: number): bigint =>
        j < ps.length ? BigInt(v.args[ps[j]]) : BigInt(value);
      const kids = t.args.map((a, i) => {
        const j = ps.indexOf(i);
        if (j < 0) return gen(a, v.args[i], 1);
        const pluck: Node = {
          paramType: Encoding.Static,
          operator: Operator.Pluck,
          compValue: hexlify(Uint8Array.from([slots[j]])),
        };
        return chance(0.5)
          ? pluck
          : {
              paramType: Encoding.None,
              operator: Operator.And,
              children: chance(0.5)
                ? [pluck, gen(a, v.args[i], 2)]
                : [gen(a, v.args[i], 2), pluck],
            };
      });
      const decs = [pick([0, 6, 18]), pick([0, 6, 18])];
      const swap = chance(0.5);
      const [ref, rel] = swap ? [1, 0] : [0, 1];
      const prec = Math.max(...decs);
      const up = (j: number) => amount(j) * 10n ** BigInt(prec - decs[j]);
      const refUp = up(ref);
      const bps = refUp > 0n ? (up(rel) * 10000n) / refUp : -1n;
      const near = (): number => {
        if (bps < 0n || bps > 0xfffffff0n || chance(0.15))
          return chance(0.3) ? 0 : int(2 ** 31);
        return Math.max(0, Number(bps) + pick([-1, 0, 0, 1]));
      };
      let lo = chance(0.3) ? 0 : near();
      let hi = chance(0.3) ? 0 : near();
      if (lo === 0 && hi === 0) hi = near() || 1;
      if (lo && hi && lo > hi) [lo, hi] = [hi, lo];
      const u32 = (x: number) =>
        Uint8Array.from([x >>> 24, (x >>> 16) & 255, (x >>> 8) & 255, x & 255]);
      const ratio: Node = {
        paramType: Encoding.None,
        operator: Operator.WithinRatio,
        compValue: hexlify(
          cat(
            Uint8Array.from([slots[ref], decs[ref], slots[rel], decs[rel]]),
            u32(lo),
            u32(hi),
          ),
        ),
        np: true,
      };
      const call: Node = {
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        compValue: leadCv(t.lead),
        children: kids,
      };
      const etherPluck: Node[] = ether
        ? [
            {
              paramType: Encoding.EtherValue,
              operator: Operator.Pluck,
              compValue: hexlify(Uint8Array.from([slots[1]])),
              np: true,
            },
          ]
        : [];
      return {
        paramType: Encoding.None,
        operator: Operator.And,
        children: [call, ...etherPluck, ratio],
      };
    };
    for (let c = 0; c < TARGET; c++) {
      tags = new Set();
      cases.push(genTarget());
    }
    function genTarget(): TCase {
      const args = Array.from({ length: 1 + int(3) }, () =>
        tTy(chance(0.6) ? 1 : 2),
      );
      const t = {
        k: "call",
        args,
        lead: { n: 4, checked: false, prefix: bytes(4) },
      } as Extract<Ty, { k: "call" }>;
      let v = randVal(t) as CallVal;
      const value = pick([0, 1, 2, 500]);
      const feats: string[] = [];
      let root: Node | undefined;
      const r = int(10);
      if (r < 3) {
        // at most 3 parameters: legacy codegen runs out of stack slots for
        // more (2-3 zipped arrays, maybe one other parameter)
        const keep = chance(0.5) ? 1 : 0;
        args.splice(keep);
        v.args.splice(keep);
        ({ root, v } = withZip(t, v, () => tTy(1), keep ? 2 : 2 + int(2)));
        feats.push("Zip");
      } else if (r < 6) {
        root = withRatio(t, v, value);
        if (root) feats.push("WithinRatio");
      }
      root ??= gen(t, v);
      if (t.args.some(hasCall)) feats.push("nested calldata");
      if (chance(0.15))
        root = {
          paramType: Encoding.None,
          operator: chance(0.5) ? Operator.And : Operator.Or,
          children: injectNP([root], "root", true),
        };
      const flat = flattenCondition(strip(root)).map((f) => ({ ...f }));
      const encoded = chance(0.15)
        ? getBytes(
            abi.encode(
              args.map(abiType),
              args.map((a, i) => toEth(a, v.args[i])),
            ),
          )
        : block(args, v.args);
      let argBytes = chance(0.3) ? cat(encoded, junk(1 + int(2))) : encoded;
      if (chance(0.25)) {
        // malformed: a word set to a large or off-by-one value, a cut, a flip
        const d = Uint8Array.from(argBytes);
        const r = int(3);
        if (r === 0 && d.length >= 32) {
          const at = 32 * int(d.length / 32);
          if (at + 32 <= d.length)
            d.set(
              w32(
                pick([
                  2n ** 64n,
                  2n ** 64n - 1n,
                  2n ** 255n,
                  BigInt(d.length),
                  BigInt(d.length - 31),
                ]),
              ),
              at,
            );
          argBytes = d;
        } else if (r === 1) argBytes = d.slice(0, int(d.length + 1));
        else {
          if (d.length) d[int(d.length)] ^= 1 << int(8);
          argBytes = d;
        }
      }
      return {
        t,
        v,
        root,
        flat,
        args: argBytes,
        value,
        bal: KEYS.map(() => pick([0n, 1n, 2n, 1000n, 2n ** 128n - 1n])),
        feats,
        packed: pack(flat),
      };
    }
    /** Per case, the nested call types (each decoded by its own echo
     *  function `c<i>_<id>` / `m<i>_<id>`, the call's receiver). */
    const callIds: Map<Ty, number>[] = cases.map((k) => {
      const ids = new Map<Ty, number>();
      const walk = (t: Ty) => {
        if (t.k === "call") {
          if (!ids.has(t)) ids.set(t, ids.size);
          t.args.forEach(walk);
        }
        if (t.k === "tuple") t.cs.forEach(walk);
        if (t.k === "array") walk(t.e);
      };
      k.t.args.forEach(walk);
      return ids;
    });
    const echoFns = (name: string, args: Ty[]) => {
      const ps = (loc: string) =>
        args
          .map((a, j) => `${solT(a)}${needsLoc(a) ? " " + loc : ""} a${j}`)
          .join(", ");
      const names = args.map((_, j) => `a${j}`).join(", ");
      return (
        `function c${name}(${ps("calldata")}) external pure returns (bytes memory) { return abi.encode(${names}); }\n` +
        `function m${name}(${ps("memory")}) external pure returns (bytes memory) { return abi.encode(${names}); }`
      );
    };
    const fns = cases.map((k, i) =>
      [
        echoFns(`${i}`, k.t.args),
        ...[...callIds[i]].map(([t, id]) =>
          echoFns(`${i}_${id}`, (t as Extract<Ty, { k: "call" }>).args),
        ),
      ].join("\n"),
    );
    const source =
      `// SPDX-License-Identifier: UNLICENSED\npragma solidity ^0.8.0;\n` +
      [...structs]
        .filter(([k]) => /^S\d+$/.test(k))
        .map(([, d]) => d)
        .join("\n") +
      Array.from(
        { length: Math.ceil(fns.length / CHUNK) },
        (_, b) =>
          `\ncontract Echo${b} {\n${fns.slice(CHUNK * b, CHUNK * b + CHUNK).join("\n")}\n}\n`,
      ).join("");
    const compile = (viaIR: boolean) => {
      const input = {
        language: "Solidity",
        sources: { "Echo.sol": { content: source } },
        settings: {
          viaIR,
          optimizer: { enabled: true, runs: 200 },
          evmVersion: "cancun",
          outputSelection: { "*": { "*": ["abi", "evm.bytecode.object"] } },
        },
      };
      const r = spawnSync(SOLC, ["--standard-json"], {
        input: JSON.stringify(input),
        maxBuffer: 1 << 28,
      });
      const out = JSON.parse(String(r.stdout));
      const errors = (out.errors ?? []).filter(
        (e: any) => e.severity === "error",
      );
      return errors.length ? { errors } : out.contracts["Echo.sol"];
    };
    const codegens: { name: string; art: any }[] = [];
    for (const viaIR of [false, true]) {
      const art = compile(viaIR);
      if (art.errors) {
        if (process.env.GAP_REPORT)
          writeFileSync(process.env.GAP_REPORT + ".sol", source);
        console.log(
          `      ${viaIR ? "via-IR" : "legacy"} compile failed: ${art.errors[0].formattedMessage.slice(0, 300)}`,
        );
        continue;
      }
      codegens.push({ name: viaIR ? "via-IR" : "legacy", art });
    }
    expect(codegens.length, "the echo target compiles").to.be.greaterThan(0);

    const connection = await network.create({
      override: { blockGasLimit: GAS > 30_000_000n ? GAS : 30_000_000n },
    } as any);
    const { ethers } = connection;
    const [signer] = await ethers.getSigners();
    const lib = async (name: string) => {
      const { bytecode } = await hre.artifacts.readArtifact(name);
      const c = await new ContractFactory([], bytecode, signer).deploy();
      return c.getAddress();
    };
    const evaluator: any = await (
      await ethers.getContractFactory("MockEvaluator", {
        libraries: {
          CustomConditionChecker: await lib("CustomConditionChecker"),
          WithinRatioChecker: await lib("WithinRatioChecker"),
        },
      })
    ).deploy();
    /** Per codegen, the contract holding case i's functions. */
    const echos: {
      name: string;
      at: (i: number) => { address: string; iface: any };
    }[] = [];
    for (const g of codegens) {
      const parts: { address: string; iface: any }[] = [];
      for (let b = 0; b * CHUNK < cases.length; b++) {
        const a = g.art[`Echo${b}`];
        const c = await new ContractFactory(
          a.abi,
          "0x" + a.evm.bytecode.object,
          signer,
        ).deploy();
        parts.push({ address: await c.getAddress(), iface: c.interface });
      }
      echos.push({ name: g.name, at: (i) => parts[Math.floor(i / CHUNK)] });
    }

    /** Every tree with some branch moved to the front of each `Or` (up to
     *  64): the runs Roles could take if any passing branch may apply. */
    const branchChoices = (n: Node): Node[] => {
      const kidSets = (n.children ?? []).map(branchChoices);
      const combos: Node[][] = [[]];
      for (const ks of kidSets) {
        const next: Node[][] = [];
        for (const c of combos)
          for (const k of ks) if (next.length < 64) next.push([...c, k]);
        combos.splice(0, combos.length, ...next);
      }
      const rebuilt = combos.map((children) =>
        n.children ? { ...n, children } : n,
      );
      if (n.operator !== Operator.Or || n.paramType !== Encoding.None)
        return rebuilt;
      // an Or may take any passing branch: try each one first (keeps the
      // tree well-typed, which the SDK check requires)
      return rebuilt
        .flatMap((r) =>
          r.children!.map((first, c) => ({
            ...r,
            children: [first, ...r.children!.filter((_, j) => j !== c)],
          })),
        )
        .slice(0, 64);
    };
    const roles = async (data: Uint8Array, k: TCase, flat = k.flat) => {
      const packed = flat === k.flat ? k.packed : pack(flat);
      if (packed === undefined) return { error: "SDK check rejects" as string };
      try {
        const [st, cons] = await evaluator.evaluatePackedWith.staticCall(
          data,
          packed,
          k.value,
          KEYS,
          k.bal,
          { gasLimit: GAS },
        );
        return {
          status: Number(st),
          cons: cons.map((x: any) => `${x[0]}:${x[1]}:${x[2]}`).join(","),
        };
      } catch (e: any) {
        return { error: errName(e, evaluator.interface) };
      }
    };

    const tally: Record<string, number> = {};
    const bump = (key: string) => (tally[key] = (tally[key] ?? 0) + 1);
    const findings: string[] = [];
    const branchCases: string[] = [];

    // What each target build decodes (canonical re-encoding, or undefined
    // for a revert), and what the Lean model of solc's decoder says.
    const decodedBy: Record<string, string | undefined>[] = [];
    // The same, with nested calldata replaced by what its receiver decodes,
    // re-encoded (undefined if a receiver reverts): the plain call.
    const canonBy: Record<string, Uint8Array | undefined>[] = [];
    const REJECT = new Error("receiver rejects");
    const canonArgs = async (
      i: number,
      part: { address: string; iface: any },
      fn: string,
      types: Ty[],
      data: Uint8Array,
    ): Promise<Uint8Array> => {
      if (!types.some(hasCall)) return data;
      const vals = abi.decode(types.map(abiType), data);
      const fix = async (t: Ty, x: any): Promise<any> => {
        if (t.k === "call") {
          const inner = getBytes(x);
          if (inner.length < 4) throw REJECT;
          const sel = part.iface.getFunction(
            `${fn}${i}_${callIds[i].get(t)}`,
          )!.selector;
          let ret: string;
          try {
            ret = await ethers.provider.call({
              to: part.address,
              data: hexlify(cat(getBytes(sel), inner.slice(4))),
            });
          } catch {
            throw REJECT;
          }
          const echoed = getBytes(abi.decode(["bytes"], ret)[0]);
          return hexlify(
            cat(
              inner.slice(0, 4),
              await canonArgs(i, part, fn, t.args, echoed),
            ),
          );
        }
        if (t.k === "tuple")
          return Promise.all(t.cs.map((c, j) => fix(c, x[j])));
        if (t.k === "array") return Promise.all([...x].map((y) => fix(t.e, y)));
        return x;
      };
      const out = await Promise.all(types.map((t, j) => fix(t, vals[j])));
      return getBytes(abi.encode(types.map(abiType), out));
    };
    for (const [i, k] of cases.entries()) {
      const r: Record<string, string | undefined> = {};
      const rc: Record<string, Uint8Array | undefined> = {};
      for (const echo of echos)
        for (const fn of ["c", "m"]) {
          const part = echo.at(i);
          const sel = part.iface.getFunction(`${fn}${i}`)!.selector;
          let ret: string | undefined;
          try {
            ret = await ethers.provider.call({
              to: part.address,
              data: hexlify(cat(getBytes(sel), k.args)),
            });
          } catch {
            ret = undefined;
          }
          const where = `${echo.name} ${fn === "c" ? "calldata" : "memory"}`;
          r[where] =
            ret === undefined
              ? undefined
              : hexlify(abi.decode(["bytes"], ret)[0]);
          try {
            rc[where] =
              r[where] === undefined
                ? undefined
                : await canonArgs(i, part, fn, k.t.args, getBytes(r[where]!));
          } catch (e) {
            if (e !== REJECT) throw e;
            rc[where] = undefined;
          }
        }
      decodedBy.push(r);
      canonBy.push(rc);
    }
    if (existsSync(LEAN_BIN)) {
      const res = spawnSync(LEAN_BIN, {
        input:
          cases
            .map(
              (k) =>
                `sd ${hexlify(cat(bytes(4), k.args))} ${k.t.args.map(abiType).join(" ")}`,
            )
            .join("\n") + "\n",
        maxBuffer: 1 << 28,
      });
      expect(res.status, String(res.stderr)).to.equal(0);
      const lean = String(res.stdout).trim().split("\n");
      expect(lean.length).to.equal(cases.length);
      const modelDiffs: string[] = [];
      cases.forEach((k, i) => {
        const m = lean[i] === "none" ? undefined : "0x" + lean[i];
        for (const [where, got] of Object.entries(decodedBy[i])) {
          if (got === m) bump(`Lean decoder agrees with ${where}`);
          else if (where.endsWith("calldata") && m === undefined) {
            // calldata parameters: offsets are compared signed and added
            // with wraparound, so solc also accepts backward offsets
            bump(`${where} accepts more (backward offsets)`);
          } else {
            bump(`Lean decoder DIFFERS from ${where}`);
            modelDiffs.push(
              `${where}: solc ${got ?? "reverts"} | Lean ${m ?? "none"}\n        types ${k.t.args.map(abiType).join(",")}\n        args ${hexlify(k.args)}`,
            );
          }
        }
      });
      for (const d of modelDiffs.slice(0, 4)) console.log(`      ${d}`);
      expect(modelDiffs, "the Lean decoder is solc's").to.deep.equal([]);
    }

    for (const [i, k] of cases.entries()) {
      const r0 = await roles(cat(bytes(4), k.args), k);
      for (const f of k.feats)
        bump(
          `with ${f}: Roles ${"error" in r0 ? String(r0.error).slice(0, 30) : r0.status === 0 ? "passes" : "fails " + r0.status}`,
        );
      if ("error" in r0) {
        bump(
          r0.error === "SDK check rejects"
            ? "SDK check rejects the tree"
            : `roles reverts: ${String(r0.error).slice(0, 40)}`,
        );
        continue;
      }
      bump(`roles ${r0.status === 0 ? "passes" : "fails"}`);
      let accepted = false;
      for (const [where, decoded] of Object.entries(canonBy[i])) {
        if (decoded === undefined) {
          bump(
            `${where}: target rejects${decodedBy[i][where] === undefined ? "" : " (nested call)"}`,
          );
          continue;
        }
        accepted = true;
        const r1 = await roles(cat(bytes(4), decoded), k);
        const canon =
          "error" in r1 ? `error ${r1.error}` : `${r1.status} ${r1.cons}`;
        if (r0.status === 0) {
          let chosen = false;
          if (canon !== `0 ${r0.cons}`)
            for (const alt of branchChoices(k.root)) {
              const r2 = await roles(
                cat(bytes(4), decoded),
                k,
                flattenCondition(strip(alt)).map((f) => ({ ...f })),
              );
              if (
                !("error" in r2) &&
                `${r2.status} ${r2.cons}` === `0 ${r0.cons}`
              ) {
                chosen = true;
                break;
              }
            }
          if (chosen) {
            bump(`${where}: another Or branch`);
            branchCases.push(
              `${where}: crafted 0 ${r0.cons} | canonical ${canon}\n        types ${k.t.args.map(abiType).join(",")}\n        args ${hexlify(k.args)}`,
            );
          } else if (canon !== `0 ${r0.cons}`) {
            bump(`${where}: BYPASS`);
            findings.push(
              `${where}: crafted 0 ${r0.cons} | canonical ${canon}\n        types ${k.t.args.map(abiType).join(",")}\n        args ${hexlify(k.args)}\n        tree ${show(k.root)}\n        nodes ${JSON.stringify(k.flat).slice(0, 1500)}`,
            );
          } else bump(`${where}: agrees (passes)`);
        } else if (canon.startsWith("0 ")) bump(`${where}: Roles stricter`);
        else bump(`${where}: agrees (fails)`);
      }
      if (r0.status === 0 && accepted)
        for (const f of k.feats)
          bump(`with ${f}: Roles passes, target accepts`);
    }
    await connection.close();
    for (const [key, n] of Object.entries(tally).sort())
      console.log(`      ${key}: ${n}`);
    for (const f of findings.slice(0, 6)) console.log(`      ${f}`);
    if (process.env.GAP_REPORT) {
      writeFileSync(
        process.env.GAP_REPORT + ".target",
        findings.join("\n\n") + "\n",
      );
      writeFileSync(
        process.env.GAP_REPORT + ".branch",
        branchCases.join("\n\n") + "\n",
      );
    }
    expect(findings, findings.slice(0, 2).join("\n")).to.deep.equal([]);
  });
});
