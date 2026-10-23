#!/usr/bin/env node
/**
 * Mutation testing for the differential tests against the Lean models.
 *
 * Applies one small change at a time to SDK code that has a Lean
 * transcription (flipped comparison, && ↔ ||, dropped negation, removed early
 * return, some ↔ every, off by one, true ↔ false), runs that code's
 * differential test, and records whether the test fails (the mutant is
 * killed). A surviving mutant is either equivalent (the change does not alter
 * behavior) or a gap in the test's inputs.
 *
 *   node test/formal/mutate.mjs <target> [--limit n] [--report file]
 *
 * Targets: `normalize` (sdk-normalize.spec.ts), `check` (checkStored.ts,
 * sdk-check.spec.ts), `pack` (packConditions.ts, its byte-for-byte test).
 * Needs the Lean driver (`cd formal && lake build roles-model`). The source
 * file is restored after every mutant, also on Ctrl-C.
 */
import { spawnSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const evm = path.resolve(here, "../..");
const sdk = path.resolve(evm, "../sdk/src/main/condition");

const TARGETS = {
  normalize: {
    files: [
      "normalize/index.ts",
      "normalize/effects.ts",
      "normalize/padToMatchTypeTree.ts",
      "normalize/pushDownOr.ts",
      "conditionId.ts",
      "typeTree.ts",
    ],
    test: ["test/formal/sdk-normalize.spec.ts"],
    env: { SDK_NORMALIZE_CASES: "6000" },
  },
  check: {
    files: ["checkStored.ts"],
    test: ["test/formal/sdk-check.spec.ts", "--grep", "agrees on"],
    env: { SDK_CHECK_CASES: "1500" },
  },
  pack: {
    files: ["packConditions.ts"],
    test: ["test/formal/sdk-check.spec.ts", "--grep", "byte for byte"],
    env: { SDK_CHECK_CASES: "1500" },
  },
};

/** [name, regex, replacement]: each match position gives one mutant. */
const OPERATORS = [
  ["=== → !==", / === /g, " !== "],
  ["!== → ===", / !== /g, " === "],
  ["<= → <", / <= /g, " < "],
  ["< → <=", / < /g, " <= "],
  [">= → >", / >= /g, " > "],
  ["> → >=", / > /g, " >= "],
  ["&& → ||", / && /g, " || "],
  ["|| → &&", / \|\| /g, " && "],
  ["drop !", /(?<=[(\s])!(?=[a-zA-Z(])/g, ""],
  ["some → every", /\.some\(/g, ".every("],
  ["every → some", /\.every\(/g, ".some("],
  ["+ 1 → + 2", / \+ 1\b/g, " + 2"],
  ["- 1 → - 0", / - 1\b/g, " - 0"],
  ["true → false", /\btrue\b/g, "false"],
  ["false → true", /\bfalse\b/g, "true"],
];

/** Lines that are only an early return: remove them. */
const EARLY_RETURN = /^\s*(if \(.*\) )?return (children|condition|null|false|true|undefined|none)\b.*$/;

function mutants(src) {
  const lines = src.split("\n");
  const out = [];
  let inComment = false;
  lines.forEach((line, i) => {
    const t = line.trim();
    if (t.startsWith("/*")) inComment = true;
    const skip =
      inComment ||
      t.startsWith("//") ||
      t.startsWith("*") ||
      t.startsWith("import") ||
      t.startsWith("export type") ||
      /^(type|interface) /.test(t);
    if (t.endsWith("*/")) inComment = false;
    if (skip) return;
    const code = line.replace(/\/\/.*$/, "").replace(/(["'`]).*?\1/g, (m) => " ".repeat(m.length));
    for (const [name, re, rep] of OPERATORS) {
      for (const m of code.matchAll(re)) {
        const mutated =
          line.slice(0, m.index) + rep + line.slice(m.index + m[0].length);
        out.push({ line: i + 1, name, mutated, original: line });
      }
    }
    if (EARLY_RETURN.test(code) && !/^\s*return/.test(code))
      out.push({ line: i + 1, name: "drop early return", mutated: "", original: line });
  });
  return out.map((m) => ({
    ...m,
    src: lines.map((l, j) => (j === m.line - 1 ? m.mutated : l)).join("\n"),
  }));
}

const args = process.argv.slice(2);
const target = TARGETS[args[0]];
if (!target) {
  console.error(`usage: mutate.mjs <${Object.keys(TARGETS).join("|")}> [--limit n] [--report file]`);
  process.exit(2);
}
const limit = args.includes("--limit") ? Number(args[args.indexOf("--limit") + 1]) : Infinity;
const reportFile = args.includes("--report") ? args[args.indexOf("--report") + 1] : undefined;

function run() {
  const r = spawnSync("npx", ["hardhat", "test", ...target.test], {
    cwd: evm,
    env: { ...process.env, ...target.env },
    encoding: "utf8",
    timeout: 600_000,
  });
  const out = (r.stdout ?? "") + (r.stderr ?? "");
  if (/SyntaxError|TransformError|is not defined|Cannot find/.test(out) && r.status !== 0)
    return "invalid";
  if (r.status === 0 && /\b[1-9]\d* passing/.test(out) && !/\d+ pending/.test(out))
    return "survived";
  return r.status === 0 ? "skipped" : "killed";
}

let current;
const restore = () => {
  if (current) writeFileSync(current.file, current.src);
};
process.on("SIGINT", () => {
  restore();
  process.exit(130);
});

if (run() !== "survived") {
  console.error("the test does not pass on the unmodified code");
  process.exit(1);
}

const results = [];
for (const rel of target.files) {
  const file = path.join(sdk, rel);
  const src = readFileSync(file, "utf8");
  current = { file, src };
  const ms = mutants(src).slice(0, limit);
  for (const [k, m] of ms.entries()) {
    writeFileSync(file, m.src);
    const verdict = run();
    restore();
    results.push({ file: rel, line: m.line, op: m.name, verdict, original: m.original.trim() });
    console.log(`${rel}:${m.line} ${m.name.padEnd(18)} ${verdict.padEnd(8)} (${k + 1}/${ms.length})`);
  }
  current = undefined;
}

const count = (v) => results.filter((r) => r.verdict === v).length;
const valid = results.length - count("invalid");
console.log(
  `\n${results.length} mutants: ${count("killed")} killed, ${count("survived")} survived, ${count("invalid")} invalid` +
    (valid ? ` (score ${((100 * count("killed")) / valid).toFixed(1)}%)` : ""),
);
for (const r of results.filter((r) => r.verdict === "survived"))
  console.log(`  survived ${r.file}:${r.line} ${r.op}: ${r.original}`);
if (reportFile) writeFileSync(reportFile, JSON.stringify(results, null, 2));
