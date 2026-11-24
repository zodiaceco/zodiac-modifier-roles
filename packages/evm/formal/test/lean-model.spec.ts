/**
 * Differential test: the Lean transcription of the Roles decoder
 * (packages/evm/formal/DecoderFaithfulness/Roles.lean) against the Solidity code.
 *
 * For random ABI signatures, condition trees and calldata (well-formed, and
 * corrupted in half of the cases), every `AbiLocation.children` and
 * `AbiLocation.sliceEncoded` result computed on-chain through `MockLocator`
 * (Integrity → pack → unpack → AbiLocation) must equal the Lean model's.
 *
 * The pack test compares the Lean packing model
 * (packages/evm/formal/ConditionPacking/Model.lean) with ConditionPacker and
 * ConditionUnpacker: byte-identical buffers, and identical unpacked trees.
 *
 * Needs the Lean driver: `cd formal && lake build roles-model`. Skipped when
 * the binary is missing. `LEAN_DIFF_CASES` sets the number of cases (default
 * 300), `LEAN_DIFF_SEED` the PRNG seed.
 */
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import path from "node:path";
import { describe, it } from "node:test";
import { fileURLToPath } from "node:url";

import { network } from "hardhat";
import {
  decodeErrorResult,
  decodeFunctionResult,
  encodeAbiParameters,
  encodeFunctionData,
  parseAbiParameters,
  toHex,
  type Abi,
  type Address,
  type ContractFunctionArgs,
  type ContractFunctionName,
  type ContractFunctionReturnType,
  type Hex,
} from "viem";

import { linkIntegrity } from "../../test/setup.js";
import {
  ConditionViolationStatus as Status,
  Encoding,
  Operator,
  extractRevertData,
  flattenCondition,
} from "../../test/utils.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const LEAN_BIN = path.resolve(here, "../.lake/build/bin/roles-model");
const CASES = Number(process.env.LEAN_DIFF_CASES ?? 300);
const SEED = Number(process.env.LEAN_DIFF_SEED ?? 1);

const abiEncode = (types: string[], values: readonly unknown[]): Hex =>
  types.length === 0
    ? "0x"
    : encodeAbiParameters(parseAbiParameters(types.join(",")), values as any);

// ---------------------------------------------------------------------------
// Deterministic randomness
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
const bytes = (n: number) => Uint8Array.from({ length: n }, () => int(256));

// ---------------------------------------------------------------------------
// Random ABI types, values, condition trees
// ---------------------------------------------------------------------------

type Ty =
  | { k: "word"; abi: string }
  | { k: "bytes"; abi: "bytes" | "string" }
  | { k: "tuple"; cs: Ty[] }
  | { k: "array"; e: Ty }
  | { k: "call"; args: Ty[] };

function randTy(depth: number): Ty {
  const r = int(depth <= 0 ? 2 : 5);
  if (r === 0)
    return {
      k: "word",
      abi: ["uint256", "address", "bytes32", "bool"][int(4)],
    };
  if (r === 1) return { k: "bytes", abi: chance(0.5) ? "bytes" : "string" };
  if (r === 2)
    return {
      k: "tuple",
      cs: Array.from({ length: 1 + int(3) }, () => randTy(depth - 1)),
    };
  if (r === 3) return { k: "array", e: randTy(depth - 1) };
  return {
    k: "call",
    args: Array.from({ length: 1 + int(3) }, () => randTy(depth - 1)),
  };
}

function abiType(t: Ty): string {
  switch (t.k) {
    case "word":
      return t.abi;
    case "bytes":
      return t.abi;
    case "tuple":
      return `(${t.cs.map(abiType).join(",")})`;
    case "array":
      return `${abiType(t.e)}[]`;
    case "call":
      return "bytes";
  }
}

function randVal(t: Ty): unknown {
  switch (t.k) {
    case "word":
      if (t.abi === "address") return toHex(bytes(20));
      if (t.abi === "bool") return chance(0.5);
      if (t.abi === "bytes32") return toHex(bytes(32));
      return BigInt(toHex(bytes(32)));
    case "bytes":
      return t.abi === "bytes"
        ? toHex(bytes(int(70)))
        : Array.from({ length: int(70) }, () => "x").join("");
    case "tuple":
      return t.cs.map(randVal);
    case "array":
      return Array.from({ length: int(4) }, () => randVal(t.e));
    case "call":
      return (
        toHex(bytes(4)) +
        abiEncode(t.args.map(abiType), t.args.map(randVal)).slice(2)
      );
  }
}

type Node = {
  paramType: Encoding;
  operator: Operator;
  compValue?: Hex;
  children?: Node[];
};

/** `_slice` compValue: 2-byte shift, 1-byte size. */
const sliceCv = (shift: number, size: number) =>
  toHex(Uint8Array.from([(shift >> 8) & 0xff, shift & 0xff, size]));

const sliceOf = (paramType: Encoding, maxShift: number, child: Node): Node => ({
  paramType,
  operator: Operator.Slice,
  compValue: sliceCv(int(maxShift), 1 + int(32)),
  children: [child],
});

function condFor(t: Ty): Node {
  let node: Node;
  switch (t.k) {
    case "word":
      node = chance(0.15)
        ? sliceOf(Encoding.Static, 32, {
            paramType: Encoding.Static,
            operator: Operator.Pass,
          })
        : { paramType: Encoding.Static, operator: Operator.Pass };
      break;
    case "bytes":
      node = chance(0.15)
        ? sliceOf(Encoding.Dynamic, 80, {
            paramType: Encoding.Static,
            operator: Operator.Pass,
          })
        : { paramType: Encoding.Dynamic, operator: Operator.Pass };
      break;
    case "tuple":
      node = {
        paramType: Encoding.Tuple,
        operator: chance(0.7) ? Operator.Matches : Operator.Pass,
        children: t.cs.map(condFor),
      };
      break;
    case "array":
      node = {
        paramType: Encoding.Array,
        operator: [Operator.Pass, Operator.ArraySome, Operator.ArrayEvery][
          int(3)
        ],
        children: [condFor(t.e)],
      };
      break;
    case "call":
      node = {
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: t.args.map(condFor),
      };
      break;
  }
  // Variant: a bytes value checked under another nested-calldata
  // interpretation as well (which usually does not fit the data).
  if ((t.k === "bytes" || t.k === "call") && chance(0.25)) {
    const other = Array.from({ length: 1 + int(2) }, () => randTy(0));
    const kids = [
      node,
      {
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: other.map(condFor),
      },
    ];
    node = {
      paramType: Encoding.None,
      operator: Operator.Or,
      children: chance(0.5) ? kids : kids.reverse(),
    };
  }
  // Non-variant logical wrapper, sometimes with a non-structural sibling.
  if (chance(0.15)) {
    const kids = [node, condFor(t)];
    if (chance(0.5))
      kids.splice(int(3), 0, {
        paramType: Encoding.EtherValue,
        operator: Operator.Pass,
      });
    node = {
      paramType: Encoding.None,
      operator: chance(0.5) ? Operator.And : Operator.Or,
      children: kids,
    };
  }
  return node;
}

function corrupt(data: string): string {
  const b = Uint8Array.from(Buffer.from(data.slice(2), "hex"));
  const words = Math.floor((b.length - 4) / 32);
  const out = Array.from(b);
  const n = 1 + int(3);
  for (let i = 0; i < n; i++) {
    const r = int(4);
    if (r === 0 && words > 0) {
      // Overwrite a word with a small number (offset/length/count fuzz).
      const w = 4 + 32 * int(words);
      const v = int(b.length + 96);
      for (let j = 0; j < 32; j++) out[w + j] = 0;
      out[w + 30] = (v >> 8) & 0xff;
      out[w + 31] = v & 0xff;
    } else if (r === 1 && out.length > 4) {
      out[4 + int(out.length - 4)] = int(256);
    } else if (r === 2) {
      out.length = Math.max(4, out.length - int(64));
    } else {
      out.push(...bytes(int(64)));
    }
  }
  return toHex(Uint8Array.from(out)) as Hex;
}

/** Conditions that pass for any value of type `t`. */
function passFor(t: Ty): Node {
  switch (t.k) {
    case "word":
      return { paramType: Encoding.Static, operator: Operator.Pass };
    case "bytes":
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
        children: t.args.map(passFor),
      };
  }
}

/** The bytes a `Slice` or `Bitmask` indexes into: the word of a static
 *  value, the content of a `bytes`/`string` value. */
function contentOf(t: Ty, v: unknown): Buffer {
  if (t.k === "word")
    return Buffer.from(abiEncode([t.abi], [v]).slice(2), "hex");
  if (t.k === "bytes")
    return t.abi === "bytes"
      ? Buffer.from(String(v).slice(2), "hex")
      : Buffer.from(String(v), "utf8");
  throw new Error("no content");
}

type Connection = Awaited<ReturnType<typeof network.create>>;
type PublicClient = Awaited<ReturnType<Connection["viem"]["getPublicClient"]>>;

async function readWithGas<
  const abi extends Abi,
  functionName extends ContractFunctionName<abi, "pure" | "view">,
>(
  publicClient: PublicClient,
  contract: { address: Address; abi: abi },
  functionName: functionName,
  args: ContractFunctionArgs<abi, "pure" | "view", functionName>,
  gas: bigint,
): Promise<ContractFunctionReturnType<abi, "pure" | "view", functionName>> {
  const data = encodeFunctionData({
    abi: contract.abi,
    functionName,
    args,
  } as any);
  const res = await publicClient.call({ to: contract.address, data, gas });
  return decodeFunctionResult({
    abi: contract.abi,
    functionName,
    args,
    data: res.data ?? "0x",
  } as any) as ContractFunctionReturnType<abi, "pure" | "view", functionName>;
}

/** MockEvaluator: Integrity → pack → unpack → evaluate, on calldata. */
async function deployEvaluator(connection: Connection) {
  return connection.viem.deployContract(
    "MockEvaluator",
    [],
    await linkIntegrity(connection.viem),
  );
}

/** Bitmask compValue: 2-byte shift, mask, expected. */
const bitmaskCv = (shift: number, mask: Buffer, expected: Buffer) =>
  toHex(
    Buffer.concat([
      Buffer.from([(shift >> 8) & 0xff, shift & 0xff]),
      mask,
      expected,
    ]),
  );

/** `bitmaskSpec`: status of a Bitmask on the operand bytes `bs`. */
function bitmaskSpec(
  bs: Buffer,
  shift: number,
  mask: Buffer,
  expected: Buffer,
) {
  const n = mask.length;
  if (shift + n > bs.length) return Status.BitmaskOverflow;
  for (let j = 0; j < n; j++)
    if ((bs[shift + j] & mask[j]) !== expected[j])
      return Status.BitmaskNotAllowed;
  return Status.Ok;
}

/** A mask and an expected value that matches `bs` at `shift` (where in
 *  range), possibly with one bit flipped. */
function randBitmask(bs: Buffer, shift: number, n: number) {
  const mask = Buffer.from(bytes(n));
  const expected = Buffer.alloc(n);
  for (let j = 0; j < n; j++)
    expected[j] = shift + j < bs.length ? bs[shift + j] & mask[j] : int(256);
  if (chance(0.4)) {
    const j = int(n);
    expected[j] ^= 1 << int(8);
  }
  return { mask, expected };
}

// ---------------------------------------------------------------------------
// Test
// ---------------------------------------------------------------------------

describe("Lean model of the Roles decoder (differential)", () => {
  it(`agrees with AbiLocation on ${CASES} random cases`, async (t) => {
    if (!existsSync(LEAN_BIN)) {
      t.skip();
      return;
    }
    rand = mulberry32(SEED);

    // Fresh simulated chain every 20 cases.
    let connection: Connection | undefined;
    let publicClient!: PublicClient;
    const deployLocator = async (c: Connection) =>
      c.viem.deployContract("MockLocator", [], await linkIntegrity(c.viem));
    let locator!: Awaited<ReturnType<typeof deployLocator>>;
    const fresh = async () => {
      await connection?.close();
      connection = await network.create();
      publicClient = await connection.viem.getPublicClient();
      locator = await deployLocator(connection);
    };

    type Query = { line: string; sol: string; info: string };
    const queries: Query[] = [];
    let reverts = 0;
    const revertReasons = new Map<string, number>();
    const kinds = new Map<string, number>();
    let phase = "walk";

    try {
      for (let c = 0; c < CASES; c++) {
        if (c % 20 === 0) await fresh();
        const args = Array.from({ length: 1 + int(3) }, () => randTy(3));
        const root: Node = {
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: args.map(condFor),
        };
        const flat = flattenCondition(root as any);
        const wellFormed = (toHex(bytes(4)) +
          abiEncode(args.map(abiType), args.map(randVal)).slice(2)) as Hex;
        const data = (
          chance(0.5) ? corrupt(wellFormed) : wellFormed
        ) as Hex;
        const dataLen = (data.length - 2) / 2;
        const nodes = flat
          .map(
            (n) =>
              `${n.parent}:${n.paramType}:${n.operator}:${String(n.compValue).slice(2)}`,
          )
          .join("|");
        const kids = (i: number) =>
          flat
            .map((n, j) => ({ n, j }))
            .filter(({ n, j }) => j !== 0 && Number(n.parent) === i)
            .map(({ j }) => j);

        const ask = async (idx: number, loc: number) => {
          // Calls that burn a large gas budget make the simulator hold a lot
          // of memory; only well-formed walk queries get a high cap.
          const gas =
            phase === "walk" && data === wellFormed ? 30_000_000n : 2_000_000n;
          let sol: string;
          let childLocs: number[] | null = null;
          try {
            const [locs, overflow] = await readWithGas(
              publicClient,
              locator,
              "getChildLocations",
              [data, BigInt(loc), flat, BigInt(idx)],
              gas,
            );
            childLocs = overflow ? null : locs.map(Number);
            const size = await readWithGas(
              publicClient,
              locator,
              "getSize",
              [data, BigInt(loc), flat, BigInt(idx)],
              gas,
            );
            sol = `${childLocs === null ? "none" : childLocs.length ? childLocs.join(",") : "-"} ${size}`;
          } catch (e: any) {
            reverts++;
            const why =
              `${phase} ${data === wellFormed ? "well-formed" : "corrupted"}: ` +
              String(e?.details ?? e?.shortMessage ?? e?.message ?? e).slice(
                0,
                60,
              );
            revertReasons.set(why, (revertReasons.get(why) ?? 0) + 1);
            return null;
          }
          const kind =
            Number(flat[idx].operator) === Operator.Slice
              ? "slice"
              : Number(flat[idx].operator) === Operator.Or &&
                  kids(idx).some(
                    (k) => Number(flat[k].paramType) === Encoding.AbiEncoded,
                  )
                ? "variant"
                : "other";
          kinds.set(kind, (kinds.get(kind) ?? 0) + 1);
          queries.push({
            line: `${data} ${loc} ${idx} ${nodes}`,
            sol,
            info: `case ${c} node ${idx} @${loc} sig (${args.map(abiType).join(",")})`,
          });
          return childLocs;
        };

        // Walk the tree the way `evaluate` does, using the on-chain locations.
        let budget = 40;
        const walk = async (idx: number, loc: number): Promise<void> => {
          if (budget-- <= 0) return;
          const n = flat[idx];
          const enc = Number(n.paramType);
          const ks = kids(idx);
          if (enc === Encoding.None) {
            // size() of a logical node picks among its children (variants)
            if (idx !== 0) await ask(idx, loc);
            for (const k of ks) await walk(k, loc);
            return;
          }
          // nested AbiEncoded: children start after length word + selector
          const childLoc =
            enc === Encoding.AbiEncoded ? (idx === 0 ? 4 : loc + 32 + 4) : loc;
          if (idx !== 0) await ask(idx, loc);
          if (
            enc !== Encoding.Tuple &&
            enc !== Encoding.Array &&
            enc !== Encoding.AbiEncoded
          )
            return;
          const locs = await ask(idx, childLoc);
          if (!locs) return;
          for (let i = 0; i < locs.length && i < 6; i++)
            await walk(enc === Encoding.Array ? ks[0] : ks[i], locs[i]);
        };
        phase = "walk";
        await walk(0, 0);
        phase = "random";

        // A few arbitrary (node, location) pairs.
        for (let i = 0; i < 3; i++)
          await ask(int(flat.length), int(dataLen + 64));
      }
    } finally {
      await connection?.close();
    }

    const res = spawnSync(LEAN_BIN, {
      input: queries.map((q) => q.line).join("\n") + "\n",
      maxBuffer: 1 << 28,
    });
    assert.equal(res.status, 0, String(res.stderr));
    const out = String(res.stdout).trim().split("\n");
    assert.equal(out.length, queries.length);

    const mismatches = queries
      .map((q, i) => ({ ...q, lean: out[i] }))
      .filter((q) => q.lean !== q.sol);
    for (const [why, n] of revertReasons)
      console.log(`      skipped ${n}× ${why}`);
    for (const m of mismatches.slice(0, 10))
      console.log(`MISMATCH ${m.info}\n  sol:  ${m.sol}\n  lean: ${m.lean}`);
    console.log(
      `      ${queries.length} queries compared (${[...kinds].map(([k, n]) => `${n} ${k}`).join(", ")}), ${reverts} on-chain reverts skipped`,
    );
    assert.equal(mismatches.length, 0);
  });
  it(`Slice reads exactly the spec window (${CASES} random cases)`, async () => {
    rand = mulberry32(SEED + 1000);
    let connection: Connection | undefined;
    let publicClient!: PublicClient;
    let evaluator!: Awaited<ReturnType<typeof deployEvaluator>>;
    let checked = 0;
    const fails: string[] = [];

    try {
      for (let c = 0; c < CASES; c++) {
        if (c % 50 === 0) {
          await connection?.close();
          connection = await network.create();
          publicClient = await connection.viem.getPublicClient();
          evaluator = await deployEvaluator(connection);
        }
        const args = Array.from({ length: 1 + int(3) }, () => randTy(2));
        const target: Ty = chance(0.5)
          ? { k: "word", abi: ["uint256", "address", "bytes32", "bool"][int(4)] }
          : { k: "bytes", abi: chance(0.5) ? "bytes" : "string" };
        const at = int(args.length + 1);
        args.splice(at, 0, target);
        const vals = args.map(randVal);
        const data = (toHex(bytes(4)) +
          abiEncode(args.map(abiType), vals).slice(2)) as Hex;

        // Spec side: the bytes a Slice indexes into.
        const content = contentOf(target, vals[at]);
        const shift = int(content.length + 8);
        const size = 1 + int(32);
        const inRange = shift + size <= content.length;
        const window = inRange
          ? content.subarray(shift, shift + size)
          : Buffer.alloc(size);
        const expected = Buffer.concat([Buffer.alloc(32 - size), window]);
        const wrong = Buffer.from(expected);
        wrong[31] ^= 1;

        for (const [cv, want] of [
          [expected, inRange ? Status.Ok : Status.CalldataOverflow],
          [wrong, inRange ? Status.ParameterNotAllowed : Status.CalldataOverflow],
        ] as const) {
          const root: Node = {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: args.map((t, i) =>
              i === at
                ? {
                    paramType:
                      target.k === "word" ? Encoding.Static : Encoding.Dynamic,
                    operator: Operator.Slice,
                    compValue: sliceCv(shift, size),
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.EqualTo,
                        compValue: toHex(cv),
                      },
                    ],
                  }
                : passFor(t),
            ),
          };
          const got = Number(
            await readWithGas(
              publicClient,
              evaluator,
              "evaluate",
              [data, flattenCondition(root as any)],
              100_000_000n,
            ),
          );
          checked++;
          if (got !== want)
            fails.push(
              `case ${c}: (${args.map(abiType).join(",")}) slice arg ${at} ` +
                `shift ${shift} size ${size} len ${content.length}: ` +
                `got status ${got}, want ${want}`,
            );
        }
      }
    } finally {
      await connection?.close();
    }
    for (const f of fails.slice(0, 10)) console.log(`      MISMATCH ${f}`);
    console.log(`      ${checked} slice evaluations checked against the spec`);
    assert.equal(fails.length, 0);
  });

  it(`agrees with BitmaskChecker on ${CASES * 4} random inputs`, async (t) => {
    if (!existsSync(LEAN_BIN)) {
      t.skip();
      return;
    }
    rand = mulberry32(SEED + 2000);
    const connection = await network.create();
    type Query = { line: string; sol: string; info: string };
    const queries: Query[] = [];
    let reverts = 0;
    try {
      const mock = await connection.viem.deployContract("MockBitmask");

      for (let c = 0; c < CASES * 4; c++) {
        // The operand `check` is given: a Static value or a window of one
        // (1 to 32 bytes), or the content of a Dynamic value.
        const operand = Buffer.from(
          bytes(chance(0.5) ? 1 + int(32) : int(200)),
        );
        let n: number, shift: number;
        if (chance(0.75) && operand.length >= 1) {
          // A window inside the operand (multi-chunk when long).
          n = 1 + int(Math.min(operand.length, 96));
          shift = int(operand.length - n + 1);
        } else {
          n = chance(0.3) ? 33 + int(60) : 1 + int(32);
          shift = chance(0.8) ? int(operand.length + 2) : int(70000);
        }
        const { mask, expected } = randBitmask(operand, shift, n);
        let cv = bitmaskCv(shift, mask, expected);
        if (chance(0.05)) cv = (cv + "ab") as Hex; // odd length (Integrity rejects it)
        const operandHex = toHex(operand);
        let sol: string;
        try {
          sol = String(Number(await mock.read.check([operandHex, cv])));
        } catch {
          reverts++;
          continue;
        }
        queries.push({
          line: `bm ${operandHex} ${cv}`,
          sol,
          info: `case ${c}: len ${operand.length} shift ${shift} n ${n}`,
        });
      }
    } finally {
      await connection.close();
    }

    const res = spawnSync(LEAN_BIN, {
      input: queries.map((q) => q.line).join("\n") + "\n",
      maxBuffer: 1 << 28,
    });
    assert.equal(res.status, 0, String(res.stderr));
    const out = String(res.stdout).trim().split("\n");
    assert.equal(out.length, queries.length);
    const counts = new Map<string, number>();
    for (const q of queries) counts.set(q.sol, (counts.get(q.sol) ?? 0) + 1);
    const mismatches = queries
      .map((q, i) => ({ ...q, lean: out[i] }))
      .filter((q) => q.lean !== q.sol);
    for (const m of mismatches.slice(0, 10))
      console.log(`MISMATCH ${m.info}\n  sol:  ${m.sol}\n  lean: ${m.lean}`);
    console.log(
      `      ${queries.length} bitmask checks compared (status ${[...counts]
        .map(([k, v]) => `${k}: ${v}`)
        .join(", ")}), ${reverts} on-chain reverts skipped`,
    );
    assert.equal(mismatches.length, 0);
  });

  it(`Bitmask checks exactly the spec bits (${CASES} random cases)`, async () => {
    rand = mulberry32(SEED + 3000);
    let connection: Connection | undefined;
    let publicClient!: PublicClient;
    let evaluator!: Awaited<ReturnType<typeof deployEvaluator>>;
    let checked = 0;
    const fails: string[] = [];
    const counts = new Map<number, number>();

    try {
      for (let c = 0; c < CASES; c++) {
        if (c % 50 === 0) {
          await connection?.close();
          connection = await network.create();
          publicClient = await connection.viem.getPublicClient();
          evaluator = await deployEvaluator(connection);
        }
        const args = Array.from({ length: 1 + int(3) }, () => randTy(2));
        const target: Ty = chance(0.5)
          ? { k: "word", abi: ["uint256", "address", "bytes32", "bool"][int(4)] }
          : { k: "bytes", abi: chance(0.5) ? "bytes" : "string" };
        const at = int(args.length + 1);
        args.splice(at, 0, target);
        const vals = args.map(randVal);
        const data = (toHex(bytes(4)) +
          abiEncode(args.map(abiType), vals).slice(2)) as Hex;
        const content = contentOf(target, vals[at]);
        const paramType =
          target.k === "word" ? Encoding.Static : Encoding.Dynamic;

        // Operand: the content, or (below a Slice) a window of it.
        let operand = content;
        let slice: { shift: number; size: number } | undefined;
        if (chance(0.3)) {
          slice = { shift: int(content.length + 4), size: 1 + int(32) };
          operand =
            slice.shift + slice.size <= content.length
              ? content.subarray(slice.shift, slice.shift + slice.size)
              : Buffer.alloc(0);
        }
        let n: number, shift: number;
        if (chance(0.75) && operand.length >= 1) {
          n = 1 + int(Math.min(operand.length, 72));
          shift = int(operand.length - n + 1);
        } else {
          n = chance(0.3) ? 33 + int(40) : 1 + int(32);
          shift = int(operand.length + 3);
        }
        const { mask, expected } = randBitmask(operand, shift, n);
        const want =
          slice && slice.shift + slice.size > content.length
            ? Status.CalldataOverflow
            : bitmaskSpec(operand, shift, mask, expected);

        const bitmask: Node = {
          paramType: slice ? Encoding.Static : paramType,
          operator: Operator.Bitmask,
          compValue: bitmaskCv(shift, mask, expected),
        };
        const root: Node = {
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: args.map((t, i) =>
            i !== at
              ? passFor(t)
              : slice
                ? {
                    paramType,
                    operator: Operator.Slice,
                    compValue: sliceCv(slice.shift, slice.size),
                    children: [bitmask],
                  }
                : bitmask,
          ),
        };
        const got = Number(
          await readWithGas(
            publicClient,
            evaluator,
            "evaluate",
            [data, flattenCondition(root as any)],
            100_000_000n,
          ),
        );
        checked++;
        counts.set(want, (counts.get(want) ?? 0) + 1);
        if (got !== want)
          fails.push(
            `case ${c}: (${args.map(abiType).join(",")}) bitmask arg ${at} ` +
              `${slice ? `slice ${slice.shift}/${slice.size} ` : ""}shift ${shift} n ${n} ` +
              `len ${content.length}: got status ${got}, want ${want}`,
          );
      }
    } finally {
      await connection?.close();
    }
    for (const f of fails.slice(0, 10)) console.log(`      MISMATCH ${f}`);
    console.log(
      `      ${checked} bitmask evaluations checked against the spec (want ${[
        ...counts,
      ]
        .map(([k, v]) => `${k}: ${v}`)
        .join(", ")})`,
    );
    assert.equal(fails.length, 0);
  });

  it(`Zip evaluates the spec elements (${CASES} random cases)`, async () => {
    rand = mulberry32(SEED + 4000);
    let connection: Connection | undefined;
    let publicClient!: PublicClient;
    let evaluator!: Awaited<ReturnType<typeof deployEvaluator>>;
    let checked = 0;
    const fails: string[] = [];
    const counts = new Map<number, number>();

    // Element types: a word, bytes, or a tuple of those.
    const randElem = (): Ty =>
      chance(0.4)
        ? { k: "word", abi: ["uint256", "address", "bytes32"][int(3)] }
        : chance(0.3)
          ? { k: "bytes", abi: chance(0.5) ? "bytes" : "string" }
          : {
              k: "tuple",
              cs: Array.from({ length: 1 + int(3) }, () =>
                chance(0.5)
                  ? { k: "word", abi: "uint256" }
                  : { k: "bytes", abi: "bytes" },
              ) as Ty[],
            };
    // Path to the first word inside an element type, if any.
    const wordPath = (t: Ty): number[] | undefined => {
      if (t.k === "word") return [];
      if (t.k === "tuple")
        for (let i = 0; i < t.cs.length; i++) {
          const p = wordPath(t.cs[i]);
          if (p) return [i, ...p];
        }
      return undefined;
    };
    const at = (v: unknown, p: number[]): unknown =>
      p.reduce((x: any, i) => x[i], v);
    const setAt = (v: unknown, p: number[], x: unknown): unknown =>
      p.length === 0
        ? x
        : (v as unknown[]).map((c, i) =>
            i === p[0] ? setAt(c, p.slice(1), x) : c,
          );
    // Conditions on an element: EqualTo `x` on the word at `p`.
    const check = (t: Ty, p: number[], x: Hex): Node => {
      if (p.length === 0)
        return {
          paramType: Encoding.Static,
          operator: Operator.EqualTo,
          compValue: x,
        };
      if (t.k !== "tuple") throw new Error("path");
      return {
        paramType: Encoding.Tuple,
        operator: Operator.Matches,
        children: t.cs.map((c, i) =>
          i === p[0] ? check(c, p.slice(1), x) : passFor(c),
        ),
      };
    };
    const wordAbi = (t: Ty, p: number[]): string =>
      p.length === 0
        ? (t as any).abi
        : wordAbi((t as any).cs[p[0]], p.slice(1));

    try {
      for (let c = 0; c < CASES; c++) {
        if (c % 50 === 0) {
          await connection?.close();
          connection = await network.create();
          publicClient = await connection.viem.getPublicClient();
          evaluator = await deployEvaluator(connection);
        }
        const k = 2 + int(2); // zipped arrays
        const elems = Array.from({ length: k }, randElem);
        const len = int(4);
        const lens = elems.map(() => (chance(0.8) ? len : int(4)));
        const zipped = elems.map((e, f) =>
          Array.from({ length: lens[f] }, () => randVal(e)),
        );

        // Check one field: EqualTo `x` on the first word inside it.
        const f0 = elems.findIndex((e) => wordPath(e) !== undefined);
        const every = chance(0.5);
        let fields = elems.map(passFor);
        let pred = (_i: number) => true;
        if (f0 >= 0) {
          const p = wordPath(elems[f0])!;
          const abi = wordAbi(elems[f0], p);
          const els = zipped[f0];
          const x =
            els.length > 0 && chance(0.7)
              ? at(els[int(els.length)], p)
              : randVal({ k: "word", abi });
          // Sometimes make every element match.
          if (els.length > 0 && chance(0.3))
            for (let i = 0; i < els.length; i++) els[i] = setAt(els[i], p, x);
          const xEnc = abiEncode([abi], [x]);
          fields = fields.map((n, f) =>
            f === f0 ? check(elems[f0], p, xEnc) : n,
          );
          pred = (i) => abiEncode([abi], [at(zipped[f0][i], p)]) === xEnc;
        }

        // Other parameters around the zipped arrays.
        const others = Array.from({ length: int(3) }, () => randTy(1));
        const params: { t: Ty; zip?: number }[] = [
          ...others.map((t) => ({ t })),
          ...elems.map((e, f) => ({ t: { k: "array", e } as Ty, zip: f })),
        ];
        for (let i = params.length - 1; i > 0; i--) {
          const j = int(i + 1);
          [params[i], params[j]] = [params[j], params[i]];
        }
        const vals = params.map((p) =>
          p.zip === undefined ? randVal(p.t) : zipped[p.zip],
        );
        const data2 = (toHex(bytes(4)) +
          abiEncode(
            params.map((p) => abiType(p.t)),
            vals,
          ).slice(2)) as Hex;

        const sameLen = lens.every((l) => l === lens[0]);
        const idx = Array.from({ length: lens[0] }, (_, i) => i);
        const want = !sameLen
          ? Status.ZippedArrayLengthMismatch
          : every
            ? idx.every(pred)
              ? Status.Ok
              : Status.NotEveryZippedElementPasses
            : idx.some(pred)
              ? Status.Ok
              : Status.NoZippedElementPasses;

        const root: Node = {
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: params.map((p) =>
                p.zip === undefined
                  ? passFor(p.t)
                  : {
                      paramType: Encoding.Array,
                      operator: Operator.Pluck,
                      compValue: toHex(Uint8Array.from([p.zip])),
                      children: [passFor(elems[p.zip])],
                    },
              ),
            },
            {
              paramType: Encoding.None,
              operator: every ? Operator.ZipEvery : Operator.ZipSome,
              compValue: toHex(Uint8Array.from(elems.map((_, f) => f))),
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Matches,
                  children: fields,
                },
              ],
            },
          ],
        };
        const got = Number(
          await readWithGas(
            publicClient,
            evaluator,
            "evaluate",
            [data2, flattenCondition(root as any)],
            100_000_000n,
          ),
        );
        checked++;
        counts.set(want, (counts.get(want) ?? 0) + 1);
        if (got !== want)
          fails.push(
            `case ${c}: (${params.map((p) => abiType(p.t)).join(",")}) ` +
              `${every ? "ZipEvery" : "ZipSome"} lens ${lens.join("/")}: got status ${got}, want ${want}`,
          );
      }
    } finally {
      await connection?.close();
    }
    for (const f of fails.slice(0, 10)) console.log(`      MISMATCH ${f}`);
    console.log(
      `      ${checked} zip evaluations checked against the spec (want ${[
        ...counts,
      ]
        .map(([k, v]) => `${k}: ${v}`)
        .join(", ")})`,
    );
    assert.equal(fails.length, 0);
  });
  it(`packs and unpacks like ConditionPacker/Unpacker (${CASES} random trees)`, async (t) => {
    if (!existsSync(LEAN_BIN)) {
      t.skip();
      return;
    }
    rand = mulberry32(SEED + 7);

    // Random compValues that exercise `_transform` and every compValue
    // shape Integrity accepts.
    let pluckIndex = 0;
    const word = () => toHex(bytes(32));
    const decorate = (n: Node): Node => {
      const kids = n.children?.map(decorate);
      const d: Node = { ...n, ...(kids ? { children: kids } : {}) };
      const leaf = !kids || kids.length === 0;
      if (n.operator === Operator.Pass && leaf) {
        if (n.paramType === Encoding.Static) {
          const r = int(8);
          if (r === 0)
            return { ...d, operator: Operator.EqualTo, compValue: word() };
          if (r === 1) return { ...d, operator: Operator.EqualToAvatar };
          if (r === 2)
            return { ...d, operator: Operator.GreaterThan, compValue: word() };
          if (r === 3)
            return {
              ...d,
              operator: Operator.Bitmask,
              compValue: toHex(bytes(2 + 2 * (1 + int(32)))),
            };
          if (r === 4 && pluckIndex < 255)
            return {
              ...d,
              operator: Operator.Pluck,
              compValue: toHex(Uint8Array.from([(pluckIndex++ * 3) % 255])),
            };
          if (r === 5)
            return {
              ...d,
              operator: Operator.Custom,
              compValue: toHex(bytes(20 + int(40))),
            };
        }
        if (n.paramType === Encoding.Dynamic) {
          const r = int(3);
          if (r === 0)
            return {
              ...d,
              operator: Operator.EqualTo,
              compValue: abiEncode(["bytes"], [toHex(bytes(int(70)))]),
            };
          if (r === 1)
            return {
              ...d,
              operator: Operator.Bitmask,
              compValue: toHex(bytes(2 + 2 * (1 + int(20)))),
            };
        }
        if (n.paramType === Encoding.EtherValue && chance(0.5))
          return { ...d, operator: Operator.LessThan, compValue: word() };
      }
      if (
        n.paramType === Encoding.AbiEncoded &&
        n.operator === Operator.Matches
      ) {
        const r = int(3);
        if (r === 1) return { ...d, compValue: toHex(bytes(2)) };
        if (r === 2) {
          const lb = int(33);
          return {
            ...d,
            compValue: toHex(Uint8Array.from([0, lb, ...bytes(lb)])),
          };
        }
      }
      // EqualTo on a whole container: the inlined case keeps its first word.
      if (
        (n.paramType === Encoding.Tuple || n.paramType === Encoding.Array) &&
        chance(0.15)
      )
        return {
          ...d,
          operator: Operator.EqualTo,
          compValue: toHex(bytes(64 + 32 * int(4))),
        };
      return d;
    };

    let connection: Connection | undefined;
    let publicClient!: PublicClient;
    const deployMockPacker = async (c: Connection) =>
      c.viem.deployContract(
        "MockPackerUnpacker",
        [],
        await linkIntegrity(c.viem),
      );
    let mock!: Awaited<ReturnType<typeof deployMockPacker>>;
    const queries: { line: string; sol: string; info: string }[] = [];
    let rejected = 0;
    const rejectedBy = new Map<string, number>();
    try {
      for (let c = 0; c < CASES; c++) {
        if (c % 50 === 0) {
          await connection?.close();
          connection = await network.create();
          publicClient = await connection.viem.getPublicClient();
          mock = await deployMockPacker(connection);
        }
        pluckIndex = int(100);
        const args = Array.from({ length: 1 + int(4) }, () =>
          randTy(chance(0.7) ? 2 : 3),
        );
        const root = decorate({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: args.map(condFor),
        });
        const flat = flattenCondition(root as any);
        let sol: Hex;
        try {
          sol = await readWithGas(
            publicClient,
            mock,
            "pack",
            [flat],
            30_000_000n,
          );
        } catch (e: any) {
          rejected++;
          // rejected by Integrity, or out of gas at the limit above
          let why = /out of gas|OutOfGas/i.test(
            String(e?.details ?? e?.shortMessage ?? e?.message),
          )
            ? "out of gas"
            : "revert";
          try {
            const rd = extractRevertData(e);
            if (rd && rd !== "0x") {
              why = decodeErrorResult({ abi: mock.abi, data: rd }).errorName;
            }
          } catch {}
          rejectedBy.set(why, (rejectedBy.get(why) ?? 0) + 1);
          continue;
        }
        const nodes = flat
          .map(
            (n) =>
              `${n.parent}:${n.paramType}:${n.operator}:${String(n.compValue).slice(2)}`,
          )
          .join("|");
        queries.push({ line: `pk ${nodes}`, sol, info: `case ${c}: ${nodes}` });
        // Unpack the contract's buffer in the model, compare with the contract.
        const [unpacked, maxPluck] = await readWithGas(
          publicClient,
          mock,
          "roundtrip",
          [flat],
          30_000_000n,
        );
        queries.push({
          line: `up ${sol}`,
          sol:
            `${maxPluck} ` +
            unpacked
              .map(
                (n) =>
                  `${n.parent}:${n.encoding}:${n.operator}:${String(n.compValue).slice(2)}:${n.inlineSize > 0n ? 1 : 0}:${n.inlineSize}`,
              )
              .join("|"),
          info: `case ${c} (unpack): ${nodes}`,
        });
      }
    } finally {
      await connection?.close();
    }

    const res = spawnSync(LEAN_BIN, {
      input: queries.map((q) => q.line).join("\n") + "\n",
      maxBuffer: 1 << 28,
    });
    assert.equal(res.status, 0, String(res.stderr));
    const out = String(res.stdout).trim().split("\n");
    assert.equal(out.length, queries.length);
    const mismatches = queries
      .map((q, i) => ({ ...q, lean: out[i] }))
      .filter((q) => q.lean !== q.sol);
    for (const m of mismatches.slice(0, 5))
      console.log(`MISMATCH ${m.info}\n  sol:  ${m.sol}\n  lean: ${m.lean}`);
    console.log(
      `      ${queries.length / 2} buffers packed and unpacked, ${rejected} trees rejected by Integrity (${[...rejectedBy].map(([k, n]) => `${n} ${k}`).join(", ")})`,
    );
    assert.equal(mismatches.length, 0);
  });
});
