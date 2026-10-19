/**
 * Differential test: the Lean transcription of the Roles decoder
 * (packages/evm/formal/DecoderFaithfulness/Roles.lean) against the Solidity code.
 *
 * For random ABI signatures, condition trees and calldata (well-formed, and
 * corrupted in half of the cases), every `AbiLocation.children` and
 * `AbiLocation.size` result computed on-chain through `MockLocator`
 * (Integrity → pack → unpack → AbiLocation) must equal the Lean model's.
 *
 * Needs the Lean driver: `cd formal && lake build roles-model`. Skipped when
 * the binary is missing. `LEAN_DIFF_CASES` sets the number of cases (default
 * 300), `LEAN_DIFF_SEED` the PRNG seed.
 */
import { expect } from "chai";
import { AbiCoder, ContractFactory, hexlify } from "ethers";
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import hre, { network } from "hardhat";

import {
  ConditionViolationStatus as Status,
  Encoding,
  Operator,
  flattenCondition,
} from "../utils.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const LEAN_BIN = path.resolve(here, "../../formal/.lake/build/bin/roles-model");
const CASES = Number(process.env.LEAN_DIFF_CASES ?? 300);
const SEED = Number(process.env.LEAN_DIFF_SEED ?? 1);

const abiCoder = AbiCoder.defaultAbiCoder();

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
      if (t.abi === "address") return hexlify(bytes(20));
      if (t.abi === "bool") return chance(0.5);
      if (t.abi === "bytes32") return hexlify(bytes(32));
      return BigInt(hexlify(bytes(32)));
    case "bytes":
      return t.abi === "bytes"
        ? hexlify(bytes(int(70)))
        : Array.from({ length: int(70) }, () => "x").join("");
    case "tuple":
      return t.cs.map(randVal);
    case "array":
      return Array.from({ length: int(4) }, () => randVal(t.e));
    case "call":
      return (
        hexlify(bytes(4)) +
        abiCoder.encode(t.args.map(abiType), t.args.map(randVal)).slice(2)
      );
  }
}

type Node = {
  paramType: Encoding;
  operator: Operator;
  compValue?: string;
  children?: Node[];
};

/** `_slice` compValue: 2-byte shift, 1-byte size. */
const sliceCv = (shift: number, size: number) =>
  hexlify(Uint8Array.from([(shift >> 8) & 0xff, shift & 0xff, size]));

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
  return hexlify(Uint8Array.from(out));
}

// ---------------------------------------------------------------------------
// Test
// ---------------------------------------------------------------------------

describe("Lean model of the Roles decoder (differential)", function () {
  this.timeout(0);

  it(`agrees with AbiLocation on ${CASES} random cases`, async function () {
    if (!existsSync(LEAN_BIN)) this.skip();
    rand = mulberry32(SEED);

    // Fresh simulated chain every 20 cases.
    let connection: Awaited<ReturnType<typeof network.create>> | undefined;
    let locator: any;
    const fresh = async () => {
      await connection?.close();
      connection = await network.create();
      locator = await (
        await connection.ethers.getContractFactory("MockLocator")
      ).deploy();
    };

    type Query = { line: string; sol: string; info: string };
    const queries: Query[] = [];
    let reverts = 0;
    const revertReasons = new Map<string, number>();
    const kinds = new Map<string, number>();
    let phase = "walk";

    for (let c = 0; c < CASES; c++) {
      if (c % 20 === 0) await fresh();
      const args = Array.from({ length: 1 + int(3) }, () => randTy(3));
      const root: Node = {
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: args.map(condFor),
      };
      const flat = flattenCondition(root as any);
      const wellFormed =
        hexlify(bytes(4)) +
        abiCoder.encode(args.map(abiType), args.map(randVal)).slice(2);
      const data = chance(0.5) ? corrupt(wellFormed) : wellFormed;
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
        const gasLimit =
          phase === "walk" && data === wellFormed ? 30_000_000 : 2_000_000;
        let sol: string;
        let childLocs: number[] | null = null;
        try {
          const [locs, overflow] = await locator.getChildLocations(
            data,
            loc,
            flat,
            idx,
            { gasLimit },
          );
          childLocs = overflow ? null : locs.map(Number);
          const size = await locator.getSize(data, loc, flat, idx, {
            gasLimit,
          });
          sol = `${childLocs === null ? "none" : childLocs.length ? childLocs.join(",") : "-"} ${size}`;
        } catch (e: any) {
          reverts++;
          const why =
            `${phase} ${data === wellFormed ? "well-formed" : "corrupted"}: ` +
            String(e?.shortMessage ?? e?.message ?? e).slice(0, 60);
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

    await connection?.close();

    const res = spawnSync(LEAN_BIN, {
      input: queries.map((q) => q.line).join("\n") + "\n",
      maxBuffer: 1 << 28,
    });
    expect(res.status, String(res.stderr)).to.equal(0);
    const out = String(res.stdout).trim().split("\n");
    expect(out.length).to.equal(queries.length);

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
    expect(mismatches.length).to.equal(0);
  });
  it(`Slice reads exactly the spec window (${CASES} random cases)`, async function () {
    rand = mulberry32(SEED + 1000);
    let connection: Awaited<ReturnType<typeof network.create>> | undefined;
    let evaluator: any;
    let checked = 0;
    const fails: string[] = [];

    // Conditions that pass for any value, so only the slice decides.
    const passFor = (t: Ty): Node => {
      switch (t.k) {
        case "word":
          return { paramType: Encoding.Static, operator: Operator.Pass };
        case "bytes":
          return { paramType: Encoding.Dynamic, operator: Operator.Pass };
        case "tuple":
          return {
            paramType: Encoding.Tuple,
            operator: Operator.Matches,
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
    };

    for (let c = 0; c < CASES; c++) {
      if (c % 50 === 0) {
        await connection?.close();
        connection = await network.create();
        const { ethers } = connection;
        // Deploy the linked libraries from bytecode only (their ABIs use
        // enum types ethers cannot parse).
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
      }
      const args = Array.from({ length: 1 + int(3) }, () => randTy(2));
      const target: Ty = chance(0.5)
        ? { k: "word", abi: ["uint256", "address", "bytes32", "bool"][int(4)] }
        : { k: "bytes", abi: chance(0.5) ? "bytes" : "string" };
      const at = int(args.length + 1);
      args.splice(at, 0, target);
      const vals = args.map(randVal);
      const data =
        hexlify(bytes(4)) + abiCoder.encode(args.map(abiType), vals).slice(2);

      // Spec side: the bytes a Slice indexes into.
      const content =
        target.k === "word"
          ? Buffer.from(
              abiCoder.encode([target.abi], [vals[at]]).slice(2),
              "hex",
            )
          : target.abi === "bytes"
            ? Buffer.from(String(vals[at]).slice(2), "hex")
            : Buffer.from(String(vals[at]), "utf8");
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
                      compValue: hexlify(cv),
                    },
                  ],
                }
              : passFor(t),
          ),
        };
        const got = Number(
          await evaluator.evaluate(data, flattenCondition(root as any), {
            gasLimit: 30_000_000,
          }),
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
    await connection?.close();
    for (const f of fails.slice(0, 10)) console.log(`      MISMATCH ${f}`);
    console.log(`      ${checked} slice evaluations checked against the spec`);
    expect(fails.length).to.equal(0);
  });
});
