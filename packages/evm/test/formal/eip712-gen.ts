/**
 * Random EIP-712 typed data for the differential tests (eip712.spec.ts,
 * eip712-permissions.ts), and the Lean driver.
 */
import { AbiCoder, hexlify, toUtf8Bytes } from "ethers";
import { spawnSync } from "node:child_process";
import path from "node:path";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
export const LEAN_BIN = path.resolve(
  here,
  "../../formal/.lake/build/bin/roles-model",
);
const abi = AbiCoder.defaultAbiCoder();

function mulberry32(seed: number) {
  return () => {
    seed |= 0;
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

export type Field = { name: string; type: string };
export type Types = Record<string, Field[]>;

export function makeGen(seed: number) {
  const rand = mulberry32(seed);
  const int = (n: number) => Math.floor(rand() * n);
  const chance = (p: number) => rand() < p;
  const pick = <T>(xs: readonly T[]): T => xs[int(xs.length)];
  const randHex = (n: number) =>
    "0x" +
    Array.from({ length: n }, () =>
      int(256).toString(16).padStart(2, "0"),
    ).join("");
  const randBig = (bits: number) =>
    BigInt(randHex(Math.ceil(bits / 8))) % (1n << BigInt(bits));

  /* ------------------------------------------------------------------ types */

  const ATOMS = [
    ...[8, 16, 32, 64, 128, 160, 256].map((b) => `uint${b}`),
    ...[8, 16, 64, 128, 256].map((b) => `int${b}`),
    "address",
    "bool",
    ...[1, 4, 20, 31, 32].map((n) => `bytes${n}`),
  ];
  const NAMES = [
    "Mail",
    "Person",
    "Asset",
    "asset",
    "Order",
    "Order2",
    "Z",
    "a_b",
    "Permit",
  ];

  function randomTypes(): { types: Types; primary: string } {
    const count = 1 + int(4);
    const names: string[] = [];
    while (names.length < count) {
      const n = pick(NAMES);
      if (!names.includes(n)) names.push(n);
    }
    const leaf = () => (chance(0.75) ? pick(ATOMS) : pick(["bytes", "string"]));
    const types: Types = {};
    names.forEach((name, k) => {
      const fields: Field[] = [];
      const n = 1 + int(4);
      for (let i = 0; i < n; i++) {
        let t =
          k + 1 < count && chance(0.25)
            ? names[k + 1 + int(count - k - 1)]
            : leaf();
        // arrays of anything, nested at most twice
        for (let d = 0; d < 2 && chance(0.3); d++)
          t += chance(0.5) ? "[]" : `[${1 + int(3)}]`;
        fields.push({ name: `f${i}`, type: t });
      }
      types[name] = fields;
    });
    // every struct after the first is referenced by an earlier one, so the
    // first is the only primary type
    for (let k = 1; k < count; k++) {
      if (
        !Object.values(types).some((fs) =>
          fs.some((f) => f.type.split("[")[0] === names[k]),
        )
      ) {
        const j = int(k);
        types[names[j]].push({
          name: `r${k}`,
          type: names[k] + (chance(0.3) ? "[]" : ""),
        });
      }
    }
    return { types, primary: names[0] };
  }

  function randomDomain() {
    const domain: Record<string, any> = {};
    if (chance(0.7)) domain.name = pick(["Ether Mail", "", "Ünï"]);
    if (chance(0.6)) domain.version = pick(["1", "2.0"]);
    if (chance(0.7)) domain.chainId = pick([1, 100, 31337, 1n, 137n]);
    if (chance(0.7)) domain.verifyingContract = randHex(20);
    if (chance(0.3)) domain.salt = randHex(32);
    if (Object.keys(domain).length === 0) domain.chainId = 1;
    return domain;
  }

  /* ----------------------------------------------------------------- values */

  const parse = (t: string) => {
    const m = t.match(/^(.*)\[(\d*)\]$/);
    return m ? { elem: m[1], len: m[2] === "" ? -1 : Number(m[2]) } : null;
  };

  function randomValue(types: Types, t: string): any {
    const arr = parse(t);
    if (arr) {
      const n = arr.len >= 0 ? arr.len : int(4);
      return Array.from({ length: n }, () => randomValue(types, arr.elem));
    }
    if (types[t]) {
      return Object.fromEntries(
        types[t].map((f) => [f.name, randomValue(types, f.type)]),
      );
    }
    if (t === "string")
      return pick(["", "hello", "Ünïcødé ✓", "x".repeat(int(70))]);
    if (t === "bytes") return randHex(int(70));
    if (t === "address") return randHex(20);
    if (t === "bool") return chance(0.5);
    if (t.startsWith("uint")) return randBig(Number(t.slice(4)));
    if (t.startsWith("int")) {
      const bits = Number(t.slice(3));
      return randBig(bits) - (1n << BigInt(bits - 1));
    }
    return randHex(Number(t.slice(5))); // bytesN
  }

  /** The value in the driver's format: `a<word>`, `d<bytes>`, `l(…)`. */
  function leanValue(types: Types, t: string, v: any): string {
    const arr = parse(t);
    if (arr)
      return `l(${v.map((x: any) => leanValue(types, arr.elem, x)).join(",")})`;
    if (types[t])
      return `l(${types[t].map((f) => leanValue(types, f.type, v[f.name])).join(",")})`;
    if (t === "string") return "d" + hexlify(toUtf8Bytes(v)).slice(2);
    if (t === "bytes") return "d" + v.slice(2);
    return "a" + abi.encode([t], [v]).slice(2);
  }

  return {
    rand,
    int,
    chance,
    pick,
    randHex,
    randomTypes,
    randomDomain,
    randomValue,
    leanValue,
  };
}

export const leanDefs = (types: Types) =>
  Object.entries(types)
    .map(([n, fs]) => `${n}=${fs.map((f) => `${f.type}:${f.name}`).join(",")}`)
    .join(";");

export type Node = { parent: number; encoding: number; typeHash: string };
export const leanTypes = (ns: Node[]) =>
  ns.length === 0
    ? "-"
    : ns
        .map((n) => `${n.parent}:${n.encoding}:${n.typeHash.slice(2)}`)
        .join("|");

/** Runs the Lean driver on one query per line. */
export function lean(lines: string[]): string[] {
  const res = spawnSync(LEAN_BIN, [], {
    input: lines.join("\n") + "\n",
    encoding: "utf8",
    maxBuffer: 1 << 30,
  });
  if (res.status !== 0) throw new Error(res.stderr);
  return res.stdout.trim().split("\n");
}
