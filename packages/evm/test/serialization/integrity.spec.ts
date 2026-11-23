/**
 * Integrity: which flat condition arrays the checked setters accept.
 *
 * Every case is one tree and one expected outcome: accepted, or a named
 * error at one node. Each expectation is asserted twice:
 *
 *  1. against the SDK's `checkStored`, the transcription of the Lean-proven
 *     `ConditionCheck.checkStored`: a case that disagrees with the reference
 *     is a mistake in this file, not in the contract;
 *  2. against the contract, through `Roles.packConditions`.
 *
 * Trees are written with the small builders below. `X(node)` marks the node
 * a rejection is reported at; its BFS index is the error's first argument.
 *
 * Not covered here, because it cannot be reached through `Roles`:
 *  - the empty array (`packConditions` returns before Integrity runs);
 *  - `ConditionNodeCountExceedsMax` (decoding 65,536 nodes runs out of gas).
 */
import { expect } from "chai";
import { network } from "hardhat";

import { checkStoredConditions } from "../../../sdk/src/main/condition/checkStored.js";
import { createSetup } from "../setup.js";
import { Encoding as E, Operator as O } from "../utils.js";

const connection = await network.create();
const { ethers } = connection;
const { deployRolesMod } = createSetup(connection);

// ---------------------------------------------------------------------------
// Trees
// ---------------------------------------------------------------------------

type N = {
  paramType: E;
  operator: O;
  compValue: string;
  children: N[];
  marked?: boolean;
};

type Flat = {
  parent: number;
  paramType: number;
  operator: number;
  compValue: string;
};

const hex = (...bytes: number[]) =>
  "0x" + bytes.map((b) => b.toString(16).padStart(2, "0")).join("");
const zeros = (length: number) => "0x" + "00".repeat(length);
const word = (n = 0) => "0x" + n.toString(16).padStart(64, "0");
const cat = (...parts: string[]) =>
  "0x" + parts.map((p) => p.slice(2)).join("");

const node = (
  paramType: E,
  operator: O,
  compValue = "0x",
  children: N[] = [],
): N => ({ paramType, operator, compValue, children });

/** Marks the node a rejection is reported at. */
const X = (n: N): N => ({ ...n, marked: true });

const pass = (paramType: E, ...children: N[]) =>
  node(paramType, O.Pass, "0x", children);
/** A word and a `bytes` parameter, unchecked. */
const S = pass(E.Static);
const D = pass(E.Dynamic);

const call = (...children: N[]) =>
  node(E.AbiEncoded, O.Matches, "0x", children);
const tuple = (...children: N[]) => node(E.Tuple, O.Matches, "0x", children);
const array = (...children: N[]) => node(E.Array, O.Matches, "0x", children);
const and = (...children: N[]) => node(E.None, O.And, "0x", children);
const or = (...children: N[]) => node(E.None, O.Or, "0x", children);

const eq = (n = 1) => node(E.Static, O.EqualTo, word(n));
const gt = (n = 1) => node(E.Static, O.GreaterThan, word(n));
/** A check on `msg.value`: reads no calldata. */
const ether = node(E.EtherValue, O.LessThan, word(1));
const slice = (child: N = eq(), paramType: E = E.Static) =>
  node(paramType, O.Slice, hex(0, 0, 1), [child]);

const pluck = (slot: number, paramType: E = E.Static) =>
  node(paramType, O.Pluck, hex(slot));
/** Plucks an array; `element` describes its element type (default: word). */
const plucks = (slot: number, ...element: N[]) =>
  node(E.Array, O.Pluck, hex(slot), element.length ? element : [S]);

const zipOf = (compValue: string, children: N[] = [tuple(S, S)]) =>
  node(E.None, O.ZipEvery, compValue, children);
const zip = (slots: number[], ...fields: N[]) =>
  zipOf(hex(...slots), [tuple(...fields)]);

const u32 = (n: number) => "0x" + n.toString(16).padStart(8, "0");
const ratioCv = ({
  ref = 0,
  refDecimals = 18,
  rel = 1,
  relDecimals = 6,
  min = 0,
  max = 10_000,
  adapters = "0x",
} = {}) =>
  cat(hex(ref, refDecimals, rel, relDecimals), u32(min), u32(max), adapters);
const ratio = (fields: Parameters<typeof ratioCv>[0] = {}) =>
  node(E.None, O.WithinRatio, ratioCv(fields));
/** One adapter blob of a WithinRatio compValue: length byte, then the blob. */
const adapter = (length: number) => cat(hex(length), zeros(length));

function flatten(root: N): { flat: Flat[]; marked?: number } {
  const flat: Flat[] = [];
  let marked: number | undefined;
  const queue = [{ n: root, parent: 0 }];
  for (let i = 0; i < queue.length; i++) {
    const { n, parent } = queue[i];
    flat.push({
      parent,
      paramType: n.paramType,
      operator: n.operator,
      compValue: n.compValue,
    });
    if (n.marked) {
      if (marked !== undefined) throw new Error("two marked nodes");
      marked = i;
    }
    for (const child of n.children) queue.push({ n: child, parent: i });
  }
  return { flat, marked };
}

// ---------------------------------------------------------------------------
// Contexts: where the node under test sits in an otherwise valid tree
// ---------------------------------------------------------------------------

/** As the only parameter of a call. */
const inCall = (x: N) => call(X(x));
/** Next to a call at the root: for nodes that read no calldata. */
const beside = (x: N) => and(call(S), X(x));
/** A Zip in a parameter slot, after the Plucks it reads. */
const zipIn = (z: N, ...before: N[]) =>
  call(...(before.length ? before : [plucks(0), plucks(1)]), and(D, z));
/** A WithinRatio after two plucked words. */
const ratioAfter = (r: N, a: N = pluck(0), b: N = pluck(1)) =>
  and(call(a, b), X(r));

// ---------------------------------------------------------------------------
// Expectations
// ---------------------------------------------------------------------------

const ACCEPTED = "accepted";
const NO_INDEX = ["UnsuitableRootNode", "NotBFS"];

let roles: Awaited<ReturnType<typeof deployRolesMod>>;

/** What the contract does with `flat`: `accepted`, or `Error(args)`. */
async function outcome(flat: Flat[]): Promise<string> {
  try {
    await roles.packConditions(flat);
    return ACCEPTED;
  } catch (e: any) {
    const data = e.data ?? e.info?.error?.data ?? e.error?.data;
    const parsed =
      typeof data === "string" && data.length >= 10
        ? roles.interface.parseError(data)
        : null;
    return parsed
      ? `${parsed.name}(${parsed.args.join(", ")})`
      : String(e.shortMessage ?? e.message);
  }
}

type Options = { label?: string; reference?: boolean };

/** Inside `each`, mismatches are collected, so one test reports them all. */
let collected: string[] | null = null;

async function check(flat: Flat[], expected: string, options: Options = {}) {
  const { label, reference = true } = options;
  const report = (subject: string, actual: unknown, wanted: unknown) => {
    if (actual === wanted) return;
    const message = `${label ? `${label}: ` : ""}${subject}: expected ${wanted}, got ${actual}`;
    if (collected) collected.push(message);
    else expect.fail(message);
  };
  if (reference) {
    report(
      "reference check (checkStored) accepts",
      checkStoredConditions(flat) !== undefined,
      expected === ACCEPTED,
    );
  }
  report("contract", await outcome(flat), expected);
}

/** A test over several cases. */
const each = (name: string, body: () => Promise<void>) =>
  it(name, async () => {
    collected = [];
    try {
      await body();
    } finally {
      const mismatches = collected;
      collected = null;
      if (mismatches.length) expect.fail("\n" + mismatches.join("\n"));
    }
  });

const expectAccepted = (tree: N, options?: Options) =>
  check(flatten(tree).flat, ACCEPTED, options);

/** `args` follow the index of the marked node in the error's arguments. */
async function expectRejected(
  tree: N,
  error: string,
  args: unknown[] = [],
  options?: Options,
) {
  const { flat, marked } = flatten(tree);
  if (NO_INDEX.includes(error)) {
    return check(flat, `${error}()`, options);
  }
  if (marked === undefined) throw new Error("mark the rejected node with X()");
  return check(flat, `${error}(${[marked, ...args].join(", ")})`, options);
}

const accepts = (name: string, tree: N) =>
  it(`accepts ${name}`, () => expectAccepted(tree));

const rejects = (name: string, tree: N, error: string, ...args: unknown[]) =>
  it(`rejects ${name}`, () => expectRejected(tree, error, args));

/**
 * CompValue rules of one operator: `build` places a compValue in a valid
 * tree (marking its node). A number is a compValue of that many zero bytes.
 */
function compValues(
  name: string,
  build: (compValue: string) => N,
  { ok, bad }: { ok: (number | string)[]; bad: (number | string)[] },
) {
  const cv = (v: number | string) => (typeof v === "number" ? zeros(v) : v);
  const show = (v: number | string) =>
    typeof v === "number" ? `${v} bytes` : v;
  each(name, async () => {
    for (const v of ok) {
      await expectAccepted(build(cv(v)), { label: show(v) });
    }
    for (const v of bad) {
      await expectRejected(build(cv(v)), "UnsuitableCompValue", [], {
        label: show(v),
      });
    }
  });
}

// ---------------------------------------------------------------------------

describe("Integrity", () => {
  before(async () => {
    const [owner] = await ethers.getSigners();
    roles = await deployRolesMod(owner.address, owner.address, owner.address);
  });

  after(async () => {
    await connection.close();
  });

  describe("flat array layout", () => {
    const root: Flat = {
      parent: 0,
      paramType: E.AbiEncoded,
      operator: O.Matches,
      compValue: "0x",
    };
    const child = (parent: number, paramType: E = E.Static): Flat => ({
      parent,
      paramType,
      operator: paramType === E.Tuple ? O.Matches : O.Pass,
      compValue: "0x",
    });

    it("rejects a root that is not its own parent", async () => {
      // the reference check never reads the root's parent
      await check([{ ...root, parent: 1 }, child(0)], "UnsuitableRootNode()", {
        reference: false,
      });
    });

    it("rejects a second node that is its own parent", async () => {
      await check([root, child(0), child(2)], "UnsuitableRootNode()");
    });

    it("rejects a parent that comes after its child", async () => {
      await check([root, child(2), child(0)], "NotBFS()");
    });

    it("rejects children that are not grouped by parent", async () => {
      await check(
        [root, child(0, E.Tuple), child(0, E.Tuple), child(2), child(1)],
        "NotBFS()",
      );
    });

    it("accepts 1023 children", async () => {
      const children = Array.from({ length: 1023 }, () => S);
      await expectAccepted(call(...children));
    });

    it("rejects more than 1023 children", async () => {
      const children = (count: number) =>
        Array.from({ length: count }, () => S);
      await expectRejected(
        X(call(...children(1024))),
        "ConditionChildCountExceedsMax",
      );
    });

    it("accepts the largest inlined size, 8160 bytes", async () => {
      const words = Array.from({ length: 255 }, () => S);
      await expectAccepted(call(pass(E.Tuple, ...words)));
    });

    it("rejects an inlined size above 8191 bytes", async () => {
      const words = (count: number) => Array.from({ length: count }, () => S);
      await expectRejected(
        call(X(pass(E.Tuple, ...words(256)))),
        "ConditionInlinedSizeExceedsMax",
      );
    });

    describe("compValue of up to 65535 bytes", () => {
      const unbounded: [string, (compValue: string) => N, number][] = [
        ["EqualTo:Dynamic", (cv) => node(E.Dynamic, O.EqualTo, cv), 65535],
        ["EqualTo:Tuple", (cv) => node(E.Tuple, O.EqualTo, cv, [S, D]), 65535],
        ["EqualTo:Array", (cv) => node(E.Array, O.EqualTo, cv, [S]), 65535],
        ["Bitmask", (cv) => node(E.Dynamic, O.Bitmask, cv), 65534],
        ["Custom", (cv) => node(E.Dynamic, O.Custom, cv), 65535],
        [
          "WithinAllowance",
          (cv) => node(E.Static, O.WithinAllowance, cv),
          65535,
        ],
      ];
      for (const [name, make, max] of unbounded) {
        compValues(name, (cv) => inCall(make(cv)), {
          ok: [max],
          bad: [65536],
        });
      }
    });
  });

  describe("operators and encodings", () => {
    const ANY = [
      E.None,
      E.Static,
      E.Dynamic,
      E.Tuple,
      E.Array,
      E.AbiEncoded,
      E.EtherValue,
    ];
    const WORD = [E.Static, E.EtherValue];
    const VALUE = [E.Static, E.Dynamic, E.Tuple, E.Array, E.EtherValue];

    const OPERATORS: [O, E[]][] = [
      [O.Pass, ANY],
      [O.And, [E.None]],
      [O.Or, [E.None]],
      [O.Empty, [E.None]],
      [O.Matches, [E.Tuple, E.Array, E.AbiEncoded]],
      [O.ArraySome, [E.Array]],
      [O.ArrayEvery, [E.Array]],
      [O.ArrayTailMatches, [E.Array]],
      [O.ZipSome, [E.None]],
      [O.ZipEvery, [E.None]],
      [O.Slice, [E.Static, E.Dynamic]],
      [O.Pluck, [E.Static, E.EtherValue, E.Array]],
      [O.EqualToAvatar, [E.Static]],
      [O.EqualTo, VALUE],
      [O.GreaterThan, WORD],
      [O.LessThan, WORD],
      [O.SignedIntGreaterThan, WORD],
      [O.SignedIntLessThan, WORD],
      [O.Bitmask, [E.Static, E.Dynamic]],
      [O.Custom, VALUE],
      [O.WithinRatio, [E.None]],
      [O.WithinAllowance, WORD],
      [O.CallWithinAllowance, [E.None]],
    ];

    const isZip = (operator: O) =>
      operator === O.ZipSome || operator === O.ZipEvery;
    const isLogical = (operator: O) => operator === O.And || operator === O.Or;

    /** A node of `operator` whose only possible defect is its encoding. */
    function sample(operator: O, paramType: E): N {
      const container = [E.Tuple, E.Array, E.AbiEncoded].includes(paramType);
      const children = isZip(operator)
        ? [tuple(S, S)]
        : operator === O.Slice
          ? [eq()]
          : isLogical(operator) || container
            ? [S]
            : [];
      const compValue = (() => {
        switch (operator) {
          case O.ZipSome:
          case O.ZipEvery:
            return hex(0, 1);
          case O.Slice:
            return hex(0, 0, 1);
          case O.Pluck:
            return hex(9);
          case O.EqualTo:
            return paramType === E.Dynamic || paramType === E.Array
              ? zeros(64)
              : word();
          case O.GreaterThan:
          case O.LessThan:
          case O.SignedIntGreaterThan:
          case O.SignedIntLessThan:
          case O.WithinAllowance:
          case O.CallWithinAllowance:
            return word();
          case O.Bitmask:
            return zeros(4);
          case O.Custom:
            return zeros(20);
          case O.WithinRatio:
            return ratioCv();
          default:
            return "0x";
        }
      })();
      return node(paramType, operator, compValue, children);
    }

    /** A valid tree around the sample. */
    function place(x: N): N {
      if (isZip(x.operator)) return zipIn(X(x));
      if (x.operator === O.WithinRatio) return ratioAfter(x);
      const readsCalldata =
        isLogical(x.operator) || ![E.None, E.EtherValue].includes(x.paramType);
      return readsCalldata ? inCall(x) : beside(x);
    }

    for (const [operator, encodings] of OPERATORS) {
      const allowed = encodings.map((e) => E[e]).join(", ");
      each(
        `${O[operator]} takes ${encodings === ANY ? "any encoding" : allowed}`,
        async () => {
          for (const paramType of ANY) {
            const tree = place(sample(operator, paramType));
            const label = `${O[operator]}:${E[paramType]}`;
            if (encodings.includes(paramType)) {
              await expectAccepted(tree, { label });
            } else {
              await expectRejected(tree, "UnsuitableParameterType", [], {
                label,
              });
            }
          }
        },
      );
    }

    each("rejects the placeholder operators", async () => {
      const placeholders = [
        O._Placeholder03,
        O._Placeholder09,
        O._Placeholder12,
        O._Placeholder24,
        O._Placeholder25,
        O._Placeholder26,
        O._Placeholder27,
        O._Placeholder29,
        O._Placeholder31,
      ];
      for (const operator of placeholders) {
        await expectRejected(
          inCall(node(E.Static, operator)),
          "UnsupportedOperator",
          [],
          { label: O[operator] },
        );
      }
    });
  });

  describe("compValue", () => {
    describe("operators without one", () => {
      const without: [string, N][] = [
        ["Pass", inCall(node(E.Static, O.Pass, "0x00"))],
        ["And", inCall(node(E.None, O.And, "0x00", [S]))],
        ["Or", inCall(node(E.None, O.Or, "0x00", [S]))],
        ["Empty", beside(node(E.None, O.Empty, "0x00"))],
        ["Matches:Tuple", inCall(node(E.Tuple, O.Matches, "0x00", [S]))],
        ["Matches:Array", inCall(node(E.Array, O.Matches, "0x00", [S]))],
        ["ArraySome", inCall(node(E.Array, O.ArraySome, "0x00", [S]))],
        ["ArrayEvery", inCall(node(E.Array, O.ArrayEvery, "0x00", [S]))],
        [
          "ArrayTailMatches",
          inCall(node(E.Array, O.ArrayTailMatches, "0x00", [S])),
        ],
        ["EqualToAvatar", inCall(node(E.Static, O.EqualToAvatar, "0x00"))],
      ];
      for (const [name, tree] of without) {
        rejects(`a compValue on ${name}`, tree, "UnsuitableCompValue");
      }
    });

    compValues(
      "Matches:AbiEncoded: empty, or 2 bytes of length with up to 32 leading bytes",
      (cv) => X(node(E.AbiEncoded, O.Matches, cv, [S])),
      {
        ok: [
          "0x",
          "0x0000",
          "0x0004",
          "0x0004a9059cbb",
          cat("0x0020", zeros(32)),
        ],
        bad: [
          "0x00",
          "0x0004a9059c",
          "0x0004a9059cbb00",
          cat("0x0021", zeros(33)),
        ],
      },
    );

    compValues(
      "Slice: 2 bytes of shift and a size of 1 to 32",
      (cv) => inCall(node(E.Static, O.Slice, cv, [eq()])),
      {
        ok: ["0x000001", "0x000020", "0xffff20"],
        bad: ["0x0001", "0x00000001", "0x000000", "0x000021"],
      },
    );

    compValues(
      "Pluck: one slot byte, 0 to 254",
      (cv) => inCall(node(E.Static, O.Pluck, cv)),
      { ok: ["0x00", "0xfe"], bad: ["0x", "0x0000", "0xff"] },
    );

    describe("Zip: one distinct Array Pluck slot per field, at least 2", () => {
      accepts(
        "three zipped arrays",
        zipIn(
          zipOf(hex(0, 1, 2), [tuple(S, S, S)]),
          plucks(0),
          plucks(1),
          plucks(2),
        ),
      );
      rejects("no slots", zipIn(X(zipOf("0x"))), "UnsuitableCompValue");
      rejects(
        "a single slot",
        zipIn(X(zipOf(hex(0), [tuple(S)]))),
        "UnsuitableCompValue",
      );
      rejects(
        "more slots than fields",
        zipIn(X(zipOf(hex(0, 1, 2))), plucks(0), plucks(1), plucks(2)),
        "UnsuitableCompValue",
      );
      rejects(
        "a slot zipped with itself",
        zipIn(X(zipOf(hex(0, 0)))),
        "UnsuitableCompValue",
      );
      rejects(
        "a slot no Pluck writes",
        zipIn(X(zipOf(hex(0, 7)))),
        "UnsuitableCompValue",
      );
      rejects(
        "a slot holding a word",
        zipIn(X(zipOf(hex(0, 1))), plucks(0), pluck(1)),
        "UnsuitableCompValue",
      );
    });

    describe("EqualTo", () => {
      compValues(
        "a word: 32 bytes",
        (cv) => inCall(node(E.Static, O.EqualTo, cv)),
        { ok: [32], bad: [0, 31, 33] },
      );
      compValues(
        "the ether value: 32 bytes",
        (cv) => beside(node(E.EtherValue, O.EqualTo, cv)),
        { ok: [32], bad: [0, 31, 33] },
      );
      compValues(
        "bytes: at least 64 bytes",
        (cv) => inCall(node(E.Dynamic, O.EqualTo, cv)),
        { ok: [64, 65], bad: [0, 63] },
      );
      compValues(
        "an array: at least 64 bytes",
        (cv) => inCall(node(E.Array, O.EqualTo, cv, [S])),
        { ok: [64, 96], bad: [0, 63] },
      );
      compValues(
        "a dynamic tuple: at least 64 bytes",
        (cv) => inCall(node(E.Tuple, O.EqualTo, cv, [S, D])),
        { ok: [64, 96], bad: [0, 63] },
      );
      compValues(
        "a static tuple: exactly its encoded size",
        (cv) => inCall(node(E.Tuple, O.EqualTo, cv, [S, S])),
        { ok: [64], bad: [0, 32, 63, 65, 96] },
      );
      compValues(
        "a nested static tuple: exactly its encoded size",
        (cv) => inCall(node(E.Tuple, O.EqualTo, cv, [S, pass(E.Tuple, S, S)])),
        { ok: [96], bad: [32, 64, 128] },
      );
    });

    for (const operator of [
      O.GreaterThan,
      O.LessThan,
      O.SignedIntGreaterThan,
      O.SignedIntLessThan,
    ]) {
      compValues(
        `${O[operator]}: 32 bytes`,
        (cv) => inCall(node(E.Static, operator, cv)),
        { ok: [32], bad: [0, 31, 33] },
      );
    }

    compValues(
      "Bitmask: 2 bytes of shift, then a mask and a value of equal length",
      (cv) => inCall(node(E.Static, O.Bitmask, cv)),
      { ok: [4, 6], bad: [0, 2, 3, 5] },
    );

    compValues(
      "Custom: an adapter address, then any extra bytes",
      (cv) => inCall(node(E.Static, O.Custom, cv)),
      { ok: [20, 21, 52], bad: [0, 19] },
    );

    compValues(
      "WithinAllowance: a key, optionally 2 decimals bytes, optionally an adapter",
      (cv) => inCall(node(E.Static, O.WithinAllowance, cv)),
      { ok: [32, 34, 54, 55], bad: [0, 31, 33, 35, 53] },
    );

    each("WithinAllowance: decimals of up to 27", async () => {
      const withDecimals = (base: number, param: number) =>
        inCall(
          node(E.Static, O.WithinAllowance, cat(word(), hex(base, param))),
        );
      await expectAccepted(withDecimals(27, 27));
      await expectRejected(withDecimals(28, 0), "AllowanceDecimalsExceedMax");
      await expectRejected(withDecimals(0, 28), "AllowanceDecimalsExceedMax");
    });

    compValues(
      "CallWithinAllowance: 32 bytes",
      (cv) => beside(node(E.None, O.CallWithinAllowance, cv)),
      { ok: [32], bad: [0, 31, 33] },
    );

    describe("WithinRatio", () => {
      compValues(
        "12 bytes, then up to two adapter blobs of 0 or at least 20 bytes",
        (cv) => ratioAfter(node(E.None, O.WithinRatio, cv)),
        {
          ok: [
            ratioCv(),
            ratioCv({ adapters: adapter(0) }),
            ratioCv({ adapters: cat(adapter(0), adapter(0)) }),
            ratioCv({ adapters: adapter(20) }),
            ratioCv({ adapters: cat(adapter(20), adapter(24)) }),
            ratioCv({ adapters: cat(adapter(0), adapter(20)) }),
          ],
          bad: [
            zeros(0),
            ratioCv().slice(0, -2),
            ratioCv({ adapters: adapter(19) }),
            ratioCv({ adapters: adapter(20).slice(0, -2) }),
            ratioCv({ adapters: cat(adapter(20), adapter(1)) }),
            ratioCv({ adapters: cat(adapter(0), adapter(0), adapter(0)) }),
          ],
        },
      );

      each("decimals of up to 27", async () => {
        await expectAccepted(
          ratioAfter(ratio({ refDecimals: 27, relDecimals: 27 })),
        );
        await expectRejected(
          ratioAfter(ratio({ refDecimals: 28 })),
          "AllowanceDecimalsExceedMax",
        );
        await expectRejected(
          ratioAfter(ratio({ relDecimals: 28 })),
          "AllowanceDecimalsExceedMax",
        );
      });

      each("a minimum, a maximum, or a satisfiable range", async () => {
        await expectAccepted(ratioAfter(ratio({ min: 1, max: 0 })));
        await expectAccepted(ratioAfter(ratio({ min: 0, max: 1 })));
        await expectAccepted(ratioAfter(ratio({ min: 5, max: 5 })));
        await expectRejected(
          ratioAfter(ratio({ min: 0, max: 0 })),
          "WithinRatioNoRatioProvided",
        );
        await expectRejected(
          ratioAfter(ratio({ min: 6, max: 5 })),
          "WithinRatioMinExceedsMax",
        );
      });

      each("slots that hold a word or the ether value", async () => {
        await expectAccepted(
          and(pluck(0, E.EtherValue), call(pluck(1)), ratio()),
        );
        await expectRejected(
          ratioAfter(ratio(), plucks(0), pluck(1)),
          "WithinRatioTargetNotStatic",
        );
        await expectRejected(
          ratioAfter(ratio(), pluck(0), plucks(1)),
          "WithinRatioTargetNotStatic",
        );
      });
    });
  });

  describe("children", () => {
    describe("leaves have none", () => {
      const leaves: [string, N][] = [
        ["a word", inCall(node(E.Static, O.EqualTo, word(), [S]))],
        ["bytes", inCall(node(E.Dynamic, O.Pass, "0x", [S]))],
        [
          "the ether value",
          beside(node(E.EtherValue, O.LessThan, word(), [S])),
        ],
        ["Pass:None", beside(node(E.None, O.Pass, "0x", [S]))],
        ["Empty", beside(node(E.None, O.Empty, "0x", [S]))],
        [
          "CallWithinAllowance",
          beside(node(E.None, O.CallWithinAllowance, word(), [S])),
        ],
        [
          "WithinRatio",
          ratioAfter(node(E.None, O.WithinRatio, ratioCv(), [S])),
        ],
      ];
      for (const [name, tree] of leaves) {
        rejects(`a child below ${name}`, tree, "LeafNodeCannotHaveChildren");
      }
    });

    describe("containers and logical nodes have at least one", () => {
      const childless: [string, N][] = [
        ["And", beside(and())],
        ["Or", beside(or())],
        ["the root call", X(call())],
        ["Matches:Tuple", inCall(tuple())],
        ["Matches:Array", inCall(array())],
        ["Pass:Tuple", inCall(pass(E.Tuple))],
        ["Pass:Array", inCall(pass(E.Array))],
        ["Pass:AbiEncoded", inCall(pass(E.AbiEncoded))],
        ["Pluck:Array", inCall(node(E.Array, O.Pluck, hex(0)))],
      ];
      for (const [name, tree] of childless) {
        rejects(`${name} without children`, tree, "UnsuitableChildCount");
      }
    });

    describe("ArraySome and ArrayEvery have exactly one", () => {
      for (const operator of [O.ArraySome, O.ArrayEvery]) {
        rejects(
          `${O[operator]} without a child`,
          inCall(node(E.Array, operator)),
          "UnsuitableChildCount",
        );
        rejects(
          `${O[operator]} with two children`,
          inCall(node(E.Array, operator, "0x", [S, S])),
          "UnsuitableChildCount",
        );
      }
    });

    describe("Slice has exactly one: a word leaf", () => {
      each("accepts any leaf operator on the sliced word", async () => {
        const leaves = [
          S,
          eq(),
          gt(),
          pluck(0),
          node(E.Static, O.EqualToAvatar),
          node(E.Static, O.Bitmask, zeros(4)),
          node(E.Static, O.WithinAllowance, word()),
        ];
        for (const leaf of leaves) {
          await expectAccepted(call(slice(leaf)), { label: O[leaf.operator] });
          await expectAccepted(call(slice(leaf, E.Dynamic)), {
            label: `${O[leaf.operator]} on bytes`,
          });
        }
      });
      rejects(
        "a Slice without a child",
        inCall(node(E.Static, O.Slice, hex(0, 0, 1))),
        "UnsuitableChildCount",
      );
      rejects(
        "a Slice with two children",
        inCall(node(E.Static, O.Slice, hex(0, 0, 1), [eq(), eq()])),
        "UnsuitableChildCount",
      );
      rejects("a Slice over bytes", inCall(slice(D)), "SliceChildNotStatic");
      rejects(
        "a Slice of a Slice",
        inCall(slice(slice())),
        "SliceChildNotStatic",
      );
    });

    describe("Zip has exactly one: a tuple of checks, one per array", () => {
      rejects(
        "a Zip without a child",
        zipIn(X(zipOf(hex(0, 1), []))),
        "UnsuitableChildCount",
      );
      rejects(
        "a Zip with two children",
        zipIn(X(zipOf(hex(0, 1), [tuple(S, S), tuple(S, S)]))),
        "UnsuitableChildCount",
      );
      rejects(
        "a Zip over an array",
        zipIn(X(zipOf(hex(0, 1), [pass(E.Array, S)]))),
        "UnsuitableChildTypeTree",
      );
      // the reference check does not look at the operator of the tuple
      it("rejects a Zip over a tuple compared as a whole", () =>
        expectRejected(
          zipIn(
            zipOf(hex(0, 1), [X(node(E.Tuple, O.EqualTo, zeros(64), [S, S]))]),
          ),
          "UnsupportedOperator",
          [],
          { reference: false },
        ));
      it("rejects a Zip over a tuple passed as a whole", () =>
        expectRejected(
          zipIn(zipOf(hex(0, 1), [X(pass(E.Tuple, S, S))])),
          "UnsupportedOperator",
          [],
          { reference: false },
        ));
      rejects(
        "a Zip field that reads no calldata",
        zipIn(zipOf(hex(0, 1), [X(tuple(S, ether))])),
        "UnsuitableChildCount",
      );
      rejects(
        "a Pluck below a Zip",
        zipIn(zipOf(hex(0, 1), [tuple(S, X(pluck(5)))])),
        "UnsupportedOperator",
      );
    });
  });

  describe("types", () => {
    describe("a container describes one parameter per child", () => {
      const strangers: [string, N, string?][] = [
        ["Matches:AbiEncoded with an ether check", X(call(S, ether))],
        ["Matches:Tuple with Pass:None", inCall(tuple(S, pass(E.None)))],
        ["Matches:Array with an ether check", inCall(array(S, ether))],
        ["Matches with an And of ether checks", X(call(S, and(ether)))],
        [
          "Matches:AbiEncoded with a Zip",
          X(call(plucks(0), plucks(1), zip([0, 1], S, S))),
        ],
        [
          "Matches:Tuple with a Zip",
          inCall(tuple(plucks(0), plucks(1), zip([0, 1], S, S))),
        ],
        ["Pass:Tuple with an ether check", inCall(pass(E.Tuple, S, ether))],
        [
          "EqualTo:Array with Pass:None",
          inCall(node(E.Array, O.EqualTo, zeros(64), [S, pass(E.None)])),
        ],
        [
          "Pass:AbiEncoded with an ether check",
          X(pass(E.AbiEncoded, S, ether)),
        ],
        ["Pluck:Array with Pass:None", inCall(plucks(0, S, pass(E.None)))],
      ];
      for (const [name, tree] of strangers) {
        rejects(name, tree, "UnsuitableChildCount");
      }
    });

    describe("a container read as a whole value takes a plain type description", () => {
      accepts(
        "nested plain tuples",
        call(pass(E.Tuple, pass(E.Tuple, S, D), S)),
      );
      accepts("a Slice in the description", call(pass(E.Tuple, slice(), D)));
      accepts(
        "nested calldata in the description",
        call(pass(E.Array, call(S))),
      );

      const navigating: [string, N][] = [
        ["Pass:Tuple over Matches", inCall(pass(E.Tuple, tuple(S)))],
        [
          "EqualTo:Tuple over And",
          inCall(node(E.Tuple, O.EqualTo, word(), [and(S)])),
        ],
        [
          "Custom:Array over ArraySome",
          inCall(
            node(E.Array, O.Custom, zeros(20), [
              node(E.Array, O.ArraySome, "0x", [S]),
            ]),
          ),
        ],
        ["Pluck:Array over Matches", inCall(plucks(0, tuple(S)))],
        ["Pass:AbiEncoded over Or", X(pass(E.AbiEncoded, or(S, S)))],
        [
          "Pass:Tuple over Matches, two levels down",
          call(pass(E.Tuple, X(pass(E.Tuple, tuple(S))))),
        ],
      ];
      for (const [name, tree] of navigating) {
        rejects(name, tree, "UnsuitableChildTypeTree");
      }
    });

    describe("the branches of And / Or read one value", () => {
      accepts("two checks of a word", call(and(eq(), gt())));
      accepts(
        "two checks of bytes",
        call(or(D, node(E.Dynamic, O.EqualTo, zeros(64)))),
      );
      accepts(
        "checks that read no calldata among the branches",
        call(and(S, ether, node(E.None, O.CallWithinAllowance, word()))),
      );
      accepts("bytes, as bytes and as calldata", call(and(D, call(S))));
      accepts(
        "bytes, as calldata of two signatures",
        call(or(call(S), call(D, S))),
      );
      accepts(
        "a prefix of a dynamic tuple in each branch",
        call(or(tuple(D, eq(1)), tuple(D, S, eq(2)))),
      );
      accepts(
        "a prefix of a dynamic tuple next to its full description",
        call(and(tuple(D), pass(E.Tuple, D, S))),
      );
      accepts(
        "all fields of a static tuple in each branch",
        call(and(tuple(S, eq()), tuple(gt(), S))),
      );
      accepts(
        "all fields of a nested static tuple in each branch",
        call(or(tuple(S, tuple(eq())), tuple(S, tuple(gt())))),
      );
      accepts(
        "a Slice next to a check of the whole word",
        call(and(slice(), gt())),
      );
      accepts(
        "a Slice next to a check of the whole word, inside arrays",
        call(
          and(
            node(E.Array, O.ArrayEvery, "0x", [slice()]),
            node(E.Array, O.ArraySome, "0x", [gt()]),
          ),
        ),
      );
      accepts(
        "bytes, as bytes and as calldata, inside arrays",
        call(
          and(
            node(E.Array, O.ArrayEvery, "0x", [call(S, gt())]),
            node(E.Array, O.ArraySome, "0x", [
              node(E.Dynamic, O.EqualTo, zeros(96)),
            ]),
          ),
        ),
      );
      accepts(
        "bytes, as bytes and as calldata, inside tuples",
        call(or(tuple(call(S)), tuple(D))),
      );

      const mismatched: [string, N][] = [
        ["a word and bytes", and(S, D)],
        ["a tuple and an array", or(tuple(S, D), array(S))],
        [
          "two full descriptions of different length",
          or(pass(E.Tuple, D), pass(E.Tuple, D, S)),
        ],
        ["a prefix of a static tuple", or(tuple(S), tuple(S, S))],
        ["prefixes that disagree on a field", or(tuple(D, S), tuple(D, D))],
        [
          "static tuples that disagree on a nested tuple",
          or(tuple(S, tuple(S)), tuple(S, tuple(S, S))),
        ],
        [
          "a static tuple and one with bytes in place of a field",
          or(tuple(S, tuple(S)), tuple(S, D)),
        ],
      ];
      for (const [name, branches] of mismatched) {
        rejects(name, inCall(branches), "UnsuitableChildTypeTree");
      }
    });

    describe("the children of an array describe one element type", () => {
      accepts("two checks of a word element", call(array(eq(1), eq(2))));
      accepts(
        "tail elements of one type",
        call(node(E.Array, O.ArrayTailMatches, "0x", [eq(1), gt(2)])),
      );
      accepts(
        "bytes elements, as calldata of two signatures",
        call(array(call(S), call(D))),
      );
      accepts(
        "the longest tuple prefix first",
        call(array(tuple(D, S), tuple(D))),
      );
      rejects(
        "a word and bytes",
        inCall(array(S, D)),
        "UnsuitableChildTypeTree",
      );
      rejects(
        "a shorter tuple prefix first",
        inCall(array(tuple(D), tuple(D, S))),
        "UnsuitableChildTypeTree",
      );
    });

    describe("a Zip sits in an And / Or, after the value it sits at", () => {
      accepts(
        "a Zip next to the call at the root",
        and(call(plucks(0), plucks(1)), zip([0, 1], S, eq())),
      );
      accepts("a Zip next to a bytes parameter", zipIn(zip([0, 1], S, eq())));
      accepts(
        "a Zip next to a check of the tuple holding its arrays",
        call(and(tuple(plucks(0), plucks(1), D), zip([0, 1], S, eq(7)))),
      );
      accepts(
        "a Zip next to one of its arrays",
        call(plucks(0), and(plucks(1), zip([0, 1], S, eq()))),
      );
      rejects(
        "a Zip before the value",
        call(plucks(0), plucks(1), X(and(zip([0, 1], S, S), D))),
        "UnsuitableChildTypeTree",
      );
      rejects(
        "an And of Zips only",
        and(call(plucks(0), plucks(1)), X(and(zip([0, 1], S, S)))),
        "UnsuitableChildTypeTree",
      );
      rejects(
        "a Zip next to a static value",
        call(plucks(0), plucks(1), X(and(S, zip([0, 1], S, S)))),
        "UnsuitableChildTypeTree",
      );
    });

    describe("a Zip field has the element type of its array", () => {
      const zipped = (element: N, field: N) =>
        call(plucks(0, element), plucks(1), and(D, X(zip([0, 1], field, S))));

      each("accepts a field that reads the element", async () => {
        const fits: [string, N, N][] = [
          ["a word", S, eq()],
          ["a Slice of a word", S, slice()],
          ["bytes as calldata", D, call(S)],
          ["a tuple", pass(E.Tuple, S, S), tuple(S, eq())],
          ["a prefix of a dynamic tuple", pass(E.Tuple, D, S), tuple(D)],
        ];
        for (const [label, element, field] of fits) {
          await expectAccepted(zipped(element, field), { label });
        }
      });

      each("rejects a field of another type", async () => {
        const misfits: [string, N, N][] = [
          ["bytes for a word", S, D],
          ["a word for bytes", D, eq()],
          ["a prefix of a static tuple", pass(E.Tuple, S, S), tuple(S)],
          ["a longer tuple", pass(E.Tuple, D), tuple(D, S)],
        ];
        for (const [label, element, field] of misfits) {
          await expectRejected(
            zipped(element, field),
            "UnsuitableChildTypeTree",
            [],
            { label },
          );
        }
      });
    });

    describe("the root is calldata, or reads none", () => {
      each("accepts roots that describe calldata", async () => {
        const roots: [string, N][] = [
          ["a call", call(S)],
          ["a call, unchecked", pass(E.AbiEncoded, S, D)],
          ["a call and an ether check", and(call(S), ether)],
          ["two signatures", or(call(S), call(D))],
          [
            "nested And / Or over calls",
            and(or(and(call(S), ether), call(S, S)), ether),
          ],
        ];
        for (const [label, tree] of roots) {
          await expectAccepted(tree, { label });
        }
      });

      each("accepts roots that read no calldata", async () => {
        const roots: [string, N][] = [
          ["Pass:None", pass(E.None)],
          ["an ether check", ether],
          [
            "WithinAllowance on the ether value",
            node(E.EtherValue, O.WithinAllowance, word()),
          ],
          ["CallWithinAllowance", node(E.None, O.CallWithinAllowance, word())],
          [
            "And / Or over those",
            and(
              or(ether, pass(E.None)),
              node(E.None, O.CallWithinAllowance, word()),
            ),
          ],
        ];
        for (const [label, tree] of roots) {
          await expectAccepted(tree, { label });
        }
      });

      each("rejects roots that describe a parameter", async () => {
        const roots: [string, N][] = [
          ["a word", eq()],
          ["bytes", D],
          ["a tuple", tuple(S)],
          ["an array", pass(E.Array, S)],
          ["an And over a word", and(eq())],
          ["a call and bytes", and(call(S), D)],
          ["a call or an And over a word", or(call(S), and(eq()))],
        ];
        for (const [label, tree] of roots) {
          await expectRejected(tree, "UnsuitableRootNode", [], { label });
        }
      });
    });
  });

  describe("Pluck slots", () => {
    rejects(
      "a slot written by two Plucks",
      call(pluck(0), X(pluck(0))),
      "DuplicatePluckIndex",
      0,
    );
    rejects(
      "a malformed Pluck, at its own index, wherever its reader sits",
      and(call(pluck(0), X(node(E.Static, O.Pluck, "0x"))), ratio()),
      "UnsuitableCompValue",
    );

    describe("a slot is written on every path before it is read", () => {
      accepts(
        "a read after the call that writes",
        and(call(pluck(0), pluck(1)), ratio()),
      );
      accepts(
        "a read in a later parameter",
        call(pluck(0), pluck(1), and(S, ratio())),
      );
      accepts(
        "a write below a Slice",
        and(call(slice(pluck(0)), pluck(1)), ratio()),
      );
      accepts(
        "a write below ArraySome",
        and(
          call(node(E.Array, O.ArraySome, "0x", [pluck(0)]), pluck(1)),
          ratio(),
        ),
      );
      accepts(
        "a write in the last element of ArrayTailMatches",
        and(
          call(node(E.Array, O.ArrayTailMatches, "0x", [pluck(0), pluck(1)])),
          ratio(),
        ),
      );

      rejects(
        "a read before the call that writes",
        and(X(ratio()), call(pluck(0), pluck(1))),
        "PluckNotVisitedBeforeRef",
        0,
      );
      rejects(
        "a read in an earlier parameter",
        call(pluck(0), and(S, X(ratio())), pluck(1)),
        "PluckNotVisitedBeforeRef",
        1,
      );
      rejects(
        "a slot no Pluck writes",
        and(call(pluck(0)), X(ratio())),
        "PluckNotVisitedBeforeRef",
        1,
      );
      rejects(
        "a Zip before one of its arrays",
        call(plucks(0), and(D, X(zip([0, 1], S, S))), plucks(1)),
        "PluckNotVisitedBeforeRef",
        1,
      );
      rejects(
        "a write in one Or branch only",
        and(or(call(pluck(0), pluck(1)), call(S, pluck(2))), X(ratio())),
        "PluckNotVisitedBeforeRef",
        0,
      );
      rejects(
        "a write below ArrayEvery, which passes on an empty array",
        and(
          call(node(E.Array, O.ArrayEvery, "0x", [pluck(0)]), pluck(1)),
          X(ratio()),
        ),
        "PluckNotVisitedBeforeRef",
        0,
      );
      rejects(
        "a Pluck in a type description, which is never evaluated",
        and(call(pass(E.Tuple, pluck(0), pluck(1))), X(ratio())),
        "PluckNotVisitedBeforeRef",
        0,
      );
      rejects(
        "a Pluck in the element type of a plucked array",
        and(call(plucks(5, pluck(0)), pluck(1)), X(ratio())),
        "PluckNotVisitedBeforeRef",
        0,
      );
    });
  });

  describe("scale", () => {
    const nested = (depth: number): N =>
      depth === 0 ? D : tuple(nested(depth - 1));
    const binary = (depth: number): N =>
      depth === 0 ? D : tuple(binary(depth - 1), binary(depth - 1));

    accepts("16 nested tuples", call(nested(16)));
    accepts("a binary tree of 64 nodes", call(binary(5)));
    accepts(
      "a call with 100 parameters",
      call(...Array.from({ length: 100 }, () => S)),
    );
  });
});
