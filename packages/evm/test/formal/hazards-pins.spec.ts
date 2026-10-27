/**
 * Differential test: the SDK's `permissionHazards` pin check against the
 * Lean definition the signing-route proof is about
 * (`EndToEnd.pinsArg`, packages/evm/formal/EndToEnd/Pins.lean).
 *
 * `only_flagged` proves: a signing permission can make the avatar sign a
 * `RoleTx` only if it is not pinned in the sense of `pinsArg` (or pins that
 * exact hash). The SDK decides "pinned" on its own condition tree, the Lean
 * definition on the tree the contract unpacks (with `inlined`, `size` and
 * leading bytes). For random conditions on the signing library's arguments
 * (`signMessage(bytes)` argument 0, the typed-message fallback's `types`,
 * argument 2), this checks that whenever the SDK raises no
 * `sign-message` / `sign-typed-message-types` hazard, `pinsArg` holds on
 * the packed and unpacked tree. The reverse (the SDK flags a permission
 * `pinsArg` accepts) is allowed and counted: the SDK may be stricter.
 *
 * Needs the Lean driver: `cd formal && lake build roles-model`. Skipped when
 * the binary is missing. `HAZARD_PIN_CASES` (default 3000), `HAZARD_PIN_SEED`.
 */
import { expect } from "chai";
import { AbiCoder, hexlify } from "ethers";
import { spawnSync } from "node:child_process";
import { existsSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { permissionHazards } from "../../../sdk/src/main/target/hazards.js";
import { flattenCondition } from "../../../sdk/src/main/condition/flattenCondition.js";
import { SIGN_TYPED_MESSAGE_LIB_ADDRESS } from "../../../sdk/src/main/addresses.js";
import {
  Clearance,
  Encoding,
  ExecutionOptions,
  Operator,
  type Condition,
} from "../../../sdk/src/main/types.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const LEAN_BIN = path.resolve(here, "../../formal/.lake/build/bin/roles-model");
const CASES = Number(process.env.HAZARD_PIN_CASES ?? 3000);
const SEED = Number(process.env.HAZARD_PIN_SEED ?? 1);

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
const randHex = (n: number) =>
  hexlify(Uint8Array.from({ length: n }, () => int(256))) as `0x${string}`;

const SIGN_MESSAGE = "0x85a5affe";
const TYPED = "0x2a9d0e1b"; // any other selector reaches the typed fallback

/* ------------------------------------------------------------- generators */

const node = (
  paramType: Encoding,
  operator: Operator,
  children?: Condition[],
  compValue?: `0x${string}`,
): Condition => ({
  paramType,
  operator,
  ...(compValue ? { compValue } : {}),
  ...(children ? { children } : {}),
});

const st = () => node(Encoding.Static, Operator.Pass);
const typesElement = () =>
  node(Encoding.Tuple, Operator.Pass, [st(), st(), st()]);

/** A type description of a value of the argument's kind, or a wrong one. */
function shape(kind: "bytes" | "types", depth = 0): Condition {
  const r = int(10);
  if (kind === "bytes" ? r < 6 : r < 1)
    return node(Encoding.Dynamic, Operator.Pass);
  if (kind === "types" && r < 6)
    return node(Encoding.Array, Operator.Pass, [typesElement()]);
  switch (r % 5) {
    case 0:
      return st();
    case 1: // element of other shapes, some 96 bytes inlined
      return node(Encoding.Array, Operator.Pass, [
        pick([
          () => node(Encoding.Tuple, Operator.Pass, [st(), st()]),
          () =>
            node(Encoding.Tuple, Operator.Pass, [
              st(),
              node(Encoding.Tuple, Operator.Pass, [st(), st()]),
            ]),
          () => node(Encoding.Tuple, Operator.Pass, [st(), st(), st(), st()]),
          () => st(),
          () => node(Encoding.Dynamic, Operator.Pass),
        ])(),
      ]);
    case 2:
      return node(Encoding.Tuple, Operator.Pass, [
        st(),
        node(Encoding.Dynamic, Operator.Pass),
      ]);
    case 3:
      return node(Encoding.Tuple, Operator.Pass, [st(), st()]);
    default:
      return depth < 1
        ? shape(kind, depth + 1)
        : node(Encoding.Dynamic, Operator.Pass);
  }
}

const withOp = (
  c: Condition,
  operator: Operator,
  compValue?: `0x${string}`,
): Condition => ({
  ...c,
  operator,
  ...(compValue ? { compValue } : {}),
});

const typesValue = () =>
  AbiCoder.defaultAbiCoder().encode(
    ["tuple(uint256,uint8,bytes32)[]"],
    [Array.from({ length: 1 + int(3) }, () => [int(4), int(6), randHex(32)])],
  ) as `0x${string}`;

/** A condition on the argument: a pin of the right or a wrong shape, a
 *  check that is no pin, or And/Or of those. */
function argCondition(kind: "bytes" | "types", depth = 0): Condition {
  const r = int(12);
  if (depth < 2 && r < 2) {
    const kids = Array.from({ length: 1 + int(3) }, () =>
      argCondition(kind, depth + 1),
    );
    return node(Encoding.None, r === 0 ? Operator.Or : Operator.And, kids);
  }
  const sh = shape(kind);
  if (r < 9) {
    const cv =
      sh.paramType === Encoding.Static
        ? randHex(32)
        : kind === "types" && sh.paramType === Encoding.Array
          ? typesValue()
          : randHex(32 + 32 * int(3));
    return withOp(sh, Operator.EqualTo, cv);
  }
  return sh; // Pass
}

/** An argument other than the pinned one (it only has to take its head
 *  word, or not). */
function otherArg(): Condition {
  const r = int(10);
  if (r < 6)
    return node(
      Encoding.Dynamic,
      chance(0.5) ? Operator.Pass : Operator.EqualTo,
      undefined,
      r < 3 ? undefined : randHex(64),
    );
  if (r < 7) return st();
  if (r < 8) return node(Encoding.Tuple, Operator.Pass, [st(), st()]); // inlined, 64 bytes
  if (r < 9)
    return node(Encoding.Tuple, Operator.Pass, [
      st(),
      node(Encoding.Dynamic, Operator.Pass),
    ]);
  return node(Encoding.None, pick([Operator.And, Operator.Or]), [
    node(Encoding.Dynamic, Operator.Pass),
    chance(0.7)
      ? node(Encoding.Dynamic, Operator.Pass)
      : node(Encoding.Tuple, Operator.Pass, [st(), st()]),
  ]);
}

const LEADING = [
  undefined,
  undefined,
  undefined,
  "0x0004",
  "0x0000",
  "0x0008",
] as const;

/** The calldata Matches, with the pinned argument at `i` among `n`. */
function matches(kind: "bytes" | "types", i: number): Condition {
  const n = Math.max(1, i + 1 + (chance(0.2) ? 1 : 0) - (chance(0.08) ? 1 : 0));
  const kids = Array.from({ length: n }, (_, j) =>
    j === i ? argCondition(kind) : otherArg(),
  );
  const lb = pick(LEADING) as `0x${string}` | undefined;
  return node(Encoding.AbiEncoded, Operator.Matches, kids, lb);
}

function root(kind: "bytes" | "types", i: number, depth = 0): Condition {
  const r = int(10);
  if (depth < 2 && r < 3) {
    const kids = Array.from({ length: 1 + int(3) }, () =>
      root(kind, i, depth + 1),
    );
    return node(Encoding.None, r === 0 ? Operator.Or : Operator.And, kids);
  }
  if (r === 3 && depth > 0) return node(Encoding.None, Operator.Pass);
  return matches(kind, i);
}

/* ------------------------------------------------------------------ test */

const hex = (s?: string) => (s ?? "0x").slice(2);
const nodesLine = (c: Condition) =>
  flattenCondition(c)
    .map((f) => `${f.parent}:${f.paramType}:${f.operator}:${hex(f.compValue)}`)
    .join("|");

const flagged = (c: Condition, selector: string, kind: string) =>
  permissionHazards([
    {
      address: SIGN_TYPED_MESSAGE_LIB_ADDRESS,
      clearance: Clearance.Function,
      executionOptions: ExecutionOptions.None,
      functions: [
        {
          selector: selector as `0x${string}`,
          executionOptions: ExecutionOptions.DelegateCall,
          wildcarded: false,
          condition: c,
        },
      ],
    },
  ]).some((h) => h.kind === kind);

describe("permissionHazards pins against the Lean pinsArg", function () {
  this.timeout(0);

  it(`raises no pin hazard only where pinsArg holds (${CASES} cases)`, function () {
    if (!existsSync(LEAN_BIN)) this.skip();

    const cases = Array.from({ length: CASES }, (_, k) => {
      const kind: "bytes" | "types" = k % 2 === 0 ? "bytes" : "types";
      const i = kind === "bytes" ? 0 : 2;
      const c = root(kind, i);
      const ts =
        kind === "bytes"
          ? !flagged(c, SIGN_MESSAGE, "sign-message")
          : !flagged(c, TYPED, "sign-typed-message-types");
      return { kind, i, c, ts };
    });

    const res = spawnSync(LEAN_BIN, {
      input:
        cases
          .map(
            (x) =>
              `pn ${x.i} ${x.kind === "bytes" ? "b" : "t"} ${nodesLine(x.c)}`,
          )
          .join("\n") + "\n",
      maxBuffer: 1 << 28,
    });
    expect(res.status, String(res.stderr)).to.equal(0);
    const out = String(res.stdout).trim().split("\n");
    expect(out.length).to.equal(cases.length);

    const tally = new Map<string, number>();
    const unsound: string[] = [];
    const stricter: string[] = [];
    cases.forEach((x, k) => {
      const lean = out[k];
      const key = `${x.kind} sdk=${x.ts ? "pinned" : "flagged"} lean=${lean}`;
      tally.set(key, (tally.get(key) ?? 0) + 1);
      const show = () => `${JSON.stringify(x.c)}\n    lean: ${lean}`;
      if (lean === "unpack-failed" || lean === "bad-input") return;
      if (x.ts && lean !== "1") unsound.push(show());
      if (!x.ts && lean === "1") stricter.push(show());
    });
    for (const [k, n] of [...tally].sort()) console.log(`      ${k}: ${n}`);
    if (stricter.length)
      console.log(
        `      SDK stricter than pinsArg, e.g.:\n      ${stricter[0].slice(0, 1500)}`,
      );
    expect(unsound, unsound.slice(0, 3).join("\n\n")).to.deep.equal([]);
  });
});
