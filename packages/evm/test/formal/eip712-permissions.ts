/**
 * Part 3 of eip712.spec.ts, in its own process (the SDK's authoring helpers
 * do not load under Hardhat). Prints one JSON line with the results.
 *
 * For random typed data and a random subset of scoped members:
 * `allowSignTypedMessage` + `checkAndPackCondition` must accept the
 * permission; its packed `domain` / `message` conditions must satisfy the
 * hypotheses of the Lean agreement theorem (`fit`); the evaluator model must
 * accept `encodeSignTypedMessage`'s calldata (`evb`), and reject it when a
 * scoped member of the message changes.
 *
 * Some permissions also get conditions the SDK has no helper for, written
 * by hand on top-level members of the message: a `Slice` comparing a window
 * of a word or of `bytes` / `string` content (the SDK refuses a Slice of a
 * Slice, which is one Slice; the proof covers both), and on a
 * `T[]` member two `Pluck`s and a `ZipSome` / `ZipEvery` over them. The
 * `fit` check then covers `sign_agree`'s window and Zip cases, and changing
 * a byte in the window or the zipped element must be rejected. Variants that
 * break the theorem's hypotheses (a Slice of the wrong kind, a Zip reading
 * an empty slot or with a mistyped field), packed without the SDK's check,
 * must fail `fit`.
 */
import { allowSignTypedMessage } from "../../../sdk/src/main/eip712-signer/allowSignTypedMessage";
import { encodeSignTypedMessage } from "../../../sdk/src/main/eip712-signer/encodeSignTypedMessage";
import { typesForDomain } from "../../../sdk/src/main/eip712-signer/types";
import {
  checkAndPackCondition,
  packConditions,
} from "../../../sdk/src/main/condition/packConditions";
import { flattenCondition } from "../../../sdk/src/main/condition/flattenCondition";
import { toFlatNodes } from "../../../sdk/src/main/condition/checkStored";
import { writeFileSync } from "node:fs";
import {
  AbiCoder,
  Interface,
  ParamType,
  getBytes,
  hexlify,
  toUtf8Bytes,
  zeroPadValue,
} from "ethers";
import { Encoding, Operator } from "../../../sdk/src/main/types";
import { describeStructure } from "../../../sdk/src/main/target/authoring/c/helpers/describeStructure";
import { Field, Types, lean, leanDefs, makeGen } from "./eip712-gen";

const CASES = Number(process.env.EIP712_CASES ?? 300);
const SEED = Number(process.env.EIP712_SEED ?? 1);
const lib = new Interface([
  "function signTypedMessage(bytes domain, bytes message, (uint256 parent, uint8 encoding, bytes32 typeHash)[] types)",
]);
const { int, chance, pick, randomTypes, randomDomain, randomValue, leanValue } =
  makeGen(SEED + 1000);

const abi = AbiCoder.defaultAbiCoder();
const parseArr = (t: string) => {
  const m = t.match(/^(.*)\[(\d*)\]$/);
  return m ? { elem: m[1], len: m[2] === "" ? -1 : Number(m[2]) } : null;
};
const abiType = (types: Types, t: string): string => {
  const arr = parseArr(t);
  if (arr) return `${abiType(types, arr.elem)}[${arr.len >= 0 ? arr.len : ""}]`;
  if (types[t])
    return `tuple(${types[t].map((f) => abiType(types, f.type)).join(",")})`;
  return t;
};
const hx = (n: number, bytes: number) =>
  n.toString(16).padStart(bytes * 2, "0");
const isAtom = (types: Types, t: string) =>
  !parseArr(t) && !types[t] && t !== "bytes" && t !== "string";

/** A member's bytes a Slice cuts from: the word of an atom, or the content
 *  of `bytes` / `string`. */
const sliceable = (types: Types, t: string, v: any) =>
  t === "bytes"
    ? { enc: Encoding.Dynamic, bytes: getBytes(v) }
    : t === "string"
      ? { enc: Encoding.Dynamic, bytes: toUtf8Bytes(v) }
      : isAtom(types, t)
        ? { enc: Encoding.Static, bytes: getBytes(abi.encode([t], [v])) }
        : null;

/** A value of type `t` with the byte at `pos` of its word / content
 *  changed, if the type has room for any value there. */
const flipByte = (t: string, v: any, pos: number): any => {
  if (t === "bytes") {
    const b = getBytes(v).slice();
    b[pos] ^= 0xff;
    return hexlify(b);
  }
  const word = getBytes(abi.encode([t], [v])).slice();
  word[pos] ^= 0xff;
  const m = t.match(/^(uint|bytes)(\d+)$/);
  if (m && m[1] === "uint" && pos >= 32 - Number(m[2]) / 8)
    return BigInt(hexlify(word));
  if (m && m[1] === "bytes" && pos < Number(m[2]))
    return hexlify(word.slice(0, Number(m[2])));
  if (t === "address" && pos >= 12) return hexlify(word.slice(12));
  return undefined;
};

let slices = 0;
let misfitChecks = 0;
let zips = 0;
let rejected = 0;
const rejectedExamples: string[] = [];
let negatives = 0;
const lines: string[] = [];
const expect_: string[] = [];
const labels: string[] = [];
for (let k = 0; k < CASES; k++) {
  const { types, primary } = randomTypes();
  const domain = randomDomain();
  const message = randomValue(types, primary);
  const withDomain = {
    EIP712Domain: typesForDomain(domain as any),
    ...types,
  } as Types;

  // pin a random subset of the members to the message's values
  const pinned = (fields: Field[], v: any) =>
    Object.fromEntries(
      fields.filter(() => chance(0.5)).map((f) => [f.name, v[f.name]]),
    );
  const msgScope = pinned(types[primary], message);
  const domScope = pinned(withDomain.EIP712Domain, domain);

  let packed: string;
  let perm: ReturnType<typeof allowSignTypedMessage>;
  // messages a hand-written Slice / Zip condition must reject
  const mutants: { what: string; message: any }[] = [];
  // changes to the permission that break the hypotheses of `sign_agree`
  const misfits: { what: string; change: (root: any) => void }[] = [];
  try {
    perm = allowSignTypedMessage({
      types: withDomain as any,
      domain: domScope as any,
      message: msgScope as any,
    });
    inject(types, primary, message, perm.condition, mutants, misfits);
    packed = checkAndPackCondition(perm.condition as any).packed;
  } catch (e) {
    rejected++;
    if (process.env.EIP712_DEBUG && rejected <= 4)
      console.error(
        JSON.stringify(perm!?.condition?.children?.[1], (_, x) =>
          typeof x === "bigint" ? x.toString() : x,
        ),
      );
    if (rejectedExamples.length < 3)
      rejectedExamples.push(`${e} ${JSON.stringify(types)}`);
    continue;
  }
  const data = encodeSignTypedMessage({
    domain: domain as any,
    types: withDomain as any,
    message,
  });
  if (data.slice(0, 10) !== perm.selector) {
    throw new Error(
      `selector ${data.slice(0, 10)} != permission ${perm.selector}`,
    );
  }
  const label = `${primary} ${JSON.stringify(types)} scope ${Object.keys(msgScope)}`;

  lines.push(`fit ${leanDefs(withDomain)} ${primary} ${packed}`);
  expect_.push("ok");
  labels.push(label);
  lines.push(`evb ${data} ${packed}`);
  expect_.push("0");
  labels.push(label);

  // change the type tree: the permission must reject
  {
    const args = lib.decodeFunctionData(
      "signTypedMessage",
      "0x" +
        lib.getFunction("signTypedMessage")!.selector.slice(2) +
        data.slice(10),
    );
    const nodes = args[2].map((n: any) => [n[0], n[1], n[2]]);
    const i = int(nodes.length);
    nodes[i] = [nodes[i][0], nodes[i][1], "0x" + "11".repeat(32)];
    const bad = lib.encodeFunctionData("signTypedMessage", [
      args[0],
      args[1],
      nodes,
    ]);
    lines.push(`evb ${data.slice(0, 10)}${bad.slice(10)} ${packed}`);
    expect_.push("not 0");
    labels.push(`${label} changed type node ${i}`);
    negatives++;
  }

  // change one scoped member: the permission must reject
  for (const mf of misfits) {
    const root = structuredClone(perm.condition);
    mf.change(root);
    const raw = hexlify(
      packConditions(toFlatNodes(flattenCondition(root as any))),
    );
    lines.push(`fit ${leanDefs(withDomain)} ${primary} ${raw}`);
    expect_.push("no fit");
    labels.push(`${label} ${mf.what}`);
    misfitChecks++;
  }

  for (const mu of mutants) {
    const bad = encodeSignTypedMessage({
      domain: domain as any,
      types: withDomain as any,
      message: mu.message,
    });
    lines.push(`evb ${bad} ${packed}`);
    expect_.push("not 0");
    labels.push(`${label} ${mu.what}`);
    negatives++;
  }

  const keys = Object.keys(msgScope);
  if (keys.length > 0) {
    const key = pick(keys);
    const type = types[primary].find((f) => f.name === key)!.type;
    let other = randomValue(types, type);
    for (
      let tries = 0;
      tries < 5 &&
      leanValue(types, type, other) === leanValue(types, type, message[key]);
      tries++
    ) {
      other = randomValue(types, type);
    }
    if (
      leanValue(types, type, other) !== leanValue(types, type, message[key])
    ) {
      const bad = encodeSignTypedMessage({
        domain: domain as any,
        types: withDomain as any,
        message: { ...message, [key]: other },
      });
      lines.push(`evb ${bad} ${packed}`);
      expect_.push("not 0");
      labels.push(`${label} changed ${key}`);
      negatives++;
    }
  }
}
/**
 * Adds hand-written Slice and Zip conditions to top-level members of the
 * message condition (`root.children[1]`), each `And`ed with what the SDK
 * built, and records messages they must reject.
 */
function inject(
  types: Types,
  primary: string,
  message: any,
  root: any,
  mutants: { what: string; message: any }[],
  misfits: { what: string; change: (root: any) => void }[],
) {
  const msg = root.children[1];
  let slot = 0;
  types[primary].forEach((f, k) => {
    const v = message[f.name];
    const add = (cond: any) => {
      msg.children[k] = {
        paramType: Encoding.None,
        operator: Operator.And,
        children: [msg.children[k], ...[cond].flat()],
      };
    };
    const sl = sliceable(types, f.type, v);
    if (sl && sl.bytes.length > 0 && chance(0.3)) {
      const bound = sl.enc === Encoding.Static ? 32 : sl.bytes.length;
      const sh = int(bound);
      const size = 1 + int(Math.min(32, bound - sh));
      const window = sl.bytes.slice(sh, sh + size);
      const leaf = {
        paramType: Encoding.Static,
        operator: Operator.EqualTo,
        compValue: zeroPadValue(hexlify(window), 32),
      };
      add({
        paramType: sl.enc,
        operator: Operator.Slice,
        compValue: "0x" + hx(sh, 2) + hx(size, 1),
        children: [leaf],
      });
      slices++;
      misfits.push({
        what: `slice ${f.name} as ${sl.enc === Encoding.Static ? "Dynamic" : "Static"}`,
        change: (r) => {
          const node = r.children[1].children[k].children[1];
          node.paramType =
            sl.enc === Encoding.Static ? Encoding.Dynamic : Encoding.Static;
        },
      });
      const pos = sh + int(size);
      const other = flipByte(f.type, v, pos);
      if (other !== undefined)
        mutants.push({
          what: `slice ${f.name} [${sh}, ${sh + size}) byte ${pos}`,
          message: { ...message, [f.name]: other },
        });
      return;
    }
    const arr = parseArr(f.type);
    if (arr && arr.len < 0 && slot < 6 && chance(0.5)) {
      const elemAbi = ParamType.from(abiType(types, arr.elem));
      const pluck = (s: number) => ({
        paramType: Encoding.Array,
        operator: Operator.Pluck,
        compValue: "0x" + hx(s, 1),
        children: [describeStructure(elemAbi)],
      });
      const [a, b] = [slot, slot + 1];
      slot += 2;
      // ZipSome comparing element j of both (the same array, plucked
      // twice), or ZipEvery over the element structure
      const j = v.length > 0 && isAtom(types, arr.elem) ? int(v.length) : -1;
      const field = () =>
        j >= 0
          ? {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: abi.encode([arr.elem], [v[j]]),
            }
          : describeStructure(elemAbi);
      add([
        pluck(a),
        pluck(b),
        {
          paramType: Encoding.None,
          operator: j >= 0 ? Operator.ZipSome : Operator.ZipEvery,
          compValue: "0x" + hx(a, 1) + hx(b, 1),
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
              children: [field(), field()],
            },
          ],
        },
      ]);
      zips++;
      misfits.push({
        what: `zip ${f.name} reads an empty slot`,
        change: (r) => {
          r.children[1].children[k].children[3].compValue =
            "0x" + hx(a, 1) + hx(200, 1);
        },
      });
      if (isAtom(types, arr.elem))
        misfits.push({
          what: `zip ${f.name} field typed Dynamic`,
          change: (r) => {
            r.children[1].children[k].children[3].children[0].children[0] = {
              paramType: Encoding.Dynamic,
              operator: Operator.Pass,
            };
          },
        });
      if (j >= 0) {
        const seen = new Set(v.map((x: any) => leanValue(types, arr.elem, x)));
        const other = randomValue(types, arr.elem);
        if (!seen.has(leanValue(types, arr.elem, other))) {
          const changed = [...v];
          changed[j] = other;
          mutants.push({
            what: `zip ${f.name} element ${j}`,
            message: { ...message, [f.name]: changed },
          });
        }
      }
    }
  });
}

if (process.env.EIP712_LINES)
  writeFileSync(process.env.EIP712_LINES, lines.join("\n") + "\n");
const out = lean(lines);
const failures: string[] = [];
out.forEach((o, i) => {
  const ok = expect_[i] === "not 0" ? o !== "0" : o === expect_[i];
  if (!ok && failures.length < 5)
    failures.push(
      `${lines[i].split(" ")[0]}: ${o}, expected ${expect_[i]}: ${labels[i]}`,
    );
});
console.log(
  JSON.stringify({
    checks: lines.length - negatives - misfitChecks,
    negatives,
    slices,
    zips,
    misfitChecks,
    rejected,
    rejectedExamples,
    failures,
  }),
);
