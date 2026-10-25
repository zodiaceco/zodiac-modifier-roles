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
 */
import { allowSignTypedMessage } from "../../../sdk/src/main/eip712-signer/allowSignTypedMessage";
import { encodeSignTypedMessage } from "../../../sdk/src/main/eip712-signer/encodeSignTypedMessage";
import { typesForDomain } from "../../../sdk/src/main/eip712-signer/types";
import { checkAndPackCondition } from "../../../sdk/src/main/condition/packConditions";
import { writeFileSync } from "node:fs";
import { Interface } from "ethers";
import { Field, Types, lean, leanDefs, makeGen } from "./eip712-gen";

const CASES = Number(process.env.EIP712_CASES ?? 300);
const SEED = Number(process.env.EIP712_SEED ?? 1);
const lib = new Interface([
  "function signTypedMessage(bytes domain, bytes message, (uint256 parent, uint8 encoding, bytes32 typeHash)[] types)",
]);
const { int, chance, pick, randomTypes, randomDomain, randomValue, leanValue } =
  makeGen(SEED + 1000);

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
  try {
    perm = allowSignTypedMessage({
      types: withDomain as any,
      domain: domScope as any,
      message: msgScope as any,
    });
    packed = checkAndPackCondition(perm.condition as any).packed;
  } catch (e) {
    rejected++;
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
    checks: lines.length - negatives,
    negatives,
    rejected,
    rejectedExamples,
    failures,
  }),
);
