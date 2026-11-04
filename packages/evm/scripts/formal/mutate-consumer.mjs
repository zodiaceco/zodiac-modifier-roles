#!/usr/bin/env node
/**
 * Memory-aliasing mutants of AllowanceConsumer.
 *
 * The Lean models treat the consumption list as an immutable value; the
 * Solidity gets the same behavior from copy-on-write over shared entry
 * pointers. These hand-written mutants break that in the ways memory code
 * usually breaks (an entry or the list updated in place, the free memory
 * pointer not or not fully advanced) and run each test that should notice.
 * A mutant no test kills is a gap: the proofs could not see the bug, and the
 * tests would not either.
 *
 *   node scripts/formal/mutate-consumer.mjs [--only <mutant>]
 *
 * Needs the Lean driver (`cd formal && lake build roles-model`). The source
 * is restored after every mutant, also on Ctrl-C.
 */
import { spawnSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const evm = path.resolve(here, "../..");
const integration = path.resolve(evm, "../integration-tests");
const file = path.join(evm, "contracts/common/AllowanceConsumer.sol");

const FIND_COPY = `            return (
                Consumption(
                    allowanceKey,
                    tracked.balance,
                    tracked.consumed,
                    tracked.timestamp
                ),
                index
            );`;
const COPY_HEAD = `        uint256 prevLength = consumptions.length;`;
const BUMP = `            mstore(0x40, add(result, mul(add(length, 1), 0x20)))`;

/** [name, what it breaks, original, replacement] */
const MUTANTS = [
  [
    "entry-in-place",
    "_findOrAccrue returns the tracked entry itself: consume updates an entry other lists share",
    FIND_COPY,
    `            return (tracked, index);`,
  ],
  [
    "list-in-place",
    "_copyOnWrite writes an existing key's entry into the input list and returns it",
    COPY_HEAD,
    `        if (index < consumptions.length) {
            consumptions[index] = entry;
            return consumptions;
        }
${COPY_HEAD}`,
  ],
  [
    "no-bump",
    "_copyOnWrite does not advance the free memory pointer: later allocations overwrite the list",
    BUMP,
    ``,
  ],
  [
    "short-bump",
    "_copyOnWrite reserves one word too few: the next allocation overwrites the last entry pointer",
    BUMP,
    `            mstore(0x40, add(result, mul(length, 0x20)))`,
  ],
];

const TESTS = [
  {
    name: "unit",
    cwd: evm,
    cmd: [
      "test/operators/01And.spec.ts",
      "test/operators/02Or.spec.ts",
      "test/operators/06ArraySome.spec.ts",
      "test/operators/07ArrayEvery.spec.ts",
      "test/operators/28WithinAllowance.spec.ts",
      "test/operators/30CallWithinAllowance.spec.ts",
      "test/allowance.spec.ts",
    ],
    env: {},
  },
  {
    name: "evaluate-diff",
    cwd: evm,
    cmd: [
      "test/formal/integrity-gaps.spec.ts",
      "--grep",
      "Lean model of evaluate",
    ],
    env: { GAP_EVAL: "300" },
  },
  {
    name: "batch-e2e",
    cwd: integration,
    cmd: ["test/e2e/batch.spec.ts"],
    env: { BATCH_CASES: "300" },
  },
];

function run(t) {
  const r = spawnSync("npx", ["hardhat", "test", ...t.cmd], {
    cwd: t.cwd,
    env: { ...process.env, ...t.env },
    encoding: "utf8",
    timeout: 900_000,
  });
  const out = (r.stdout ?? "") + (r.stderr ?? "");
  if (
    /Compilation failed|CompilerError|ParserError|TypeError:/.test(out) &&
    r.status !== 0
  )
    return "invalid";
  if (
    r.status === 0 &&
    /\b[1-9]\d* passing/.test(out) &&
    !/\d+ pending/.test(out)
  )
    return "survived";
  return r.status === 0 ? "skipped" : "killed";
}

const src = readFileSync(file, "utf8");
const restore = () => writeFileSync(file, src);
process.on("SIGINT", () => {
  restore();
  process.exit(130);
});

const args = process.argv.slice(2);
const only = args.includes("--only")
  ? args[args.indexOf("--only") + 1]
  : undefined;

for (const t of TESTS) {
  const v = run(t);
  if (v !== "survived") {
    console.error(`${t.name} does not pass on the unmodified code (${v})`);
    process.exit(1);
  }
}

const results = [];
for (const [name, what, from, to] of MUTANTS) {
  if (only && name !== only) continue;
  if (!src.includes(from)) throw new Error(`${name}: anchor not found`);
  writeFileSync(file, src.replace(from, to));
  const verdicts = {};
  try {
    for (const t of TESTS) verdicts[t.name] = run(t);
  } finally {
    restore();
  }
  results.push({ name, what, verdicts });
  console.log(
    `${name.padEnd(16)} ${TESTS.map((t) => `${t.name}=${verdicts[t.name]}`).join(" ")}`,
  );
}

const survivors = results.filter(
  (r) => !Object.values(r.verdicts).includes("killed"),
);
console.log(
  `\n${results.length} mutants, ${results.length - survivors.length} killed by some test`,
);
for (const r of survivors) console.log(`  survived ${r.name}: ${r.what}`);
process.exit(survivors.length ? 1 : 0);
