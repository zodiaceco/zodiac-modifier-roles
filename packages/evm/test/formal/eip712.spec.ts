/**
 * Differential tests for EIP-712 signing: the SDK's encoders
 * (packages/sdk/src/main/eip712-signer), the contract's `EIP712Encoder`
 * (through `MockEIP712Encoder`), and their Lean counterparts
 * (packages/evm/formal/EIP712), through the Lean driver.
 *
 * Random typed data: up to four structs (nested, referenced through arrays
 * and fixed-size arrays), every atomic type, `bytes` and `string`, random
 * domains. For each:
 *
 * 1. Three independent digests agree: ethers' `TypedDataEncoder` (the
 *    oracle), the Lean EIP-712 spec (`es` query), and the contract encoder
 *    fed by the SDK (`encodeTypedDomain`, `encodeTypedMessage`,
 *    `toAbiTypes`). The SDK's `hashType` agrees with the Lean `typeHash`.
 *    `_toTree` of the SDK's `toAbiTypes` output is the type tree the Lean
 *    digest theorem assumes (`lay` query, `layOf`).
 * 2. The Lean transcription of the encoder (`eh` query) returns what the
 *    contract returns, on the SDK's encoding and on mutated bytes (offsets,
 *    lengths, truncation, dirty words, changed type nodes): the same hash,
 *    or both revert.
 *
 * 3. `allowSignTypedMessage` permissions, as `checkAndPackCondition` packs
 *    them, satisfy the hypotheses of the Lean agreement theorem
 *    (`EIP712.message_agree`: the `domain` and `message` conditions follow
 *    the type trees; `fit` query), and the evaluator model accepts the
 *    SDK's `encodeSignTypedMessage` calldata for a message the scoping
 *    allows and rejects it when a scoped member changes (`evb` query).
 *
 * Needs the Lean driver: `cd formal && lake build roles-model`. Skipped when
 * it is missing. `EIP712_CASES` sets the number of typed messages (default
 * 300), `EIP712_MUTATIONS` mutations per message (default 8), `EIP712_SEED`
 * the seed.
 */
import { expect } from "chai";
import {
  AbiCoder,
  TypedDataEncoder,
  concat,
  hexlify,
  keccak256,
  toUtf8Bytes,
} from "ethers";
import { network } from "hardhat";
import { spawnSync } from "node:child_process";
import { existsSync, writeFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import {
  encodeTypedDomain,
  encodeTypedMessage,
  toAbiTypes,
} from "../../../sdk/src/main/eip712-signer/encode/index.js";
import {
  hashType,
  typesForDomain,
} from "../../../sdk/src/main/eip712-signer/types/index.js";
import {
  LEAN_BIN,
  Node,
  Types,
  Field,
  lean,
  leanDefs,
  leanTypes,
  makeGen,
} from "./eip712-gen.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const TSX = path.resolve(here, "../../node_modules/.bin/tsx");
const CASES = Number(process.env.EIP712_CASES ?? 300);
const MUTATIONS = Number(process.env.EIP712_MUTATIONS ?? 8);
const SEED = Number(process.env.EIP712_SEED ?? 1);

const { ethers } = await network.create();

const gen = makeGen(SEED);
const {
  int,
  chance,
  pick,
  randHex,
  rand,
  randomTypes,
  randomDomain,
  randomValue,
  leanValue,
} = gen;

/* -------------------------------------------------------------- mutations */

function mutateBytes(hex: string): string {
  let b = hex.slice(2);
  const words = Math.floor(b.length / 64);
  const setWord = (i: number, w: bigint) => {
    const v = w & ((1n << 256n) - 1n);
    b =
      b.slice(0, i * 64) +
      v.toString(16).padStart(64, "0") +
      b.slice(i * 64 + 64);
  };
  const kind = int(6);
  if (kind <= 2 && words > 0) {
    const i = int(words);
    const old = BigInt("0x" + b.slice(i * 64, i * 64 + 64));
    setWord(
      i,
      pick([
        0n,
        old + 32n,
        old - 32n < 0n ? 0n : old - 32n,
        old + 1n,
        BigInt(int(words + 2) * 32),
        BigInt(b.length / 2),
        (1n << 256n) - 1n,
        BigInt(randHex(32)),
      ]),
    );
  } else if (kind === 3) {
    b = b.slice(0, 2 * int(b.length / 2 + 1));
  } else if (kind === 4) {
    b += pick([
      "00".repeat(32),
      randHex(32).slice(2),
      randHex(int(40)).slice(2),
    ]);
  } else if (b.length > 0) {
    const p = int(b.length / 2);
    b = b.slice(0, 2 * p) + randHex(1).slice(2) + b.slice(2 * p + 2);
  }
  return "0x" + b;
}

function mutateTypes(ns: Node[]): Node[] {
  const out = ns.map((n) => ({ ...n }));
  if (out.length === 0) return out;
  const n = out[int(out.length)];
  const kind = int(3);
  if (kind === 0) n.encoding = int(7);
  else if (kind === 1) n.parent = int(out.length + 1);
  else n.typeHash = "0x" + "00".repeat(32);
  return out;
}

/* ----------------------------------------------------------------- tests */

const lean_ok = existsSync(LEAN_BIN);

describe("EIP-712: SDK, contract encoder and Lean", function () {
  this.timeout(0);

  before(function () {
    if (!lean_ok) this.skip();
  });

  it("digests agree with ethers and the Lean spec; the Lean encoder matches the contract", async () => {
    const encoder = await (
      await ethers.getContractFactory("MockEIP712Encoder")
    ).deploy();
    const call = async (d: string, m: string, ns: Node[]) => {
      try {
        return await encoder.hashTypedMessage(
          d,
          m,
          ns.map((n) => [n.parent, n.encoding, n.typeHash]),
        );
      } catch (e: any) {
        // only a revert of the call counts; anything else is a test bug
        if (
          !(
            e?.code === "CALL_EXCEPTION" ||
            /revert|out of gas/i.test(String(e?.message))
          )
        )
          throw e;
        return "revert";
      }
    };

    type Case = {
      oracle: string;
      sdk: string;
      domainTypes: Field[];
      types: Types;
      primary: string;
      specLine: string;
      layLine: string;
      encLines: string[];
      contract: string[];
    };
    const cases: Case[] = [];
    let mutated = 0;
    let mutatedOk = 0;

    for (let k = 0; k < CASES; k++) {
      const { types, primary } = randomTypes();
      const domain = randomDomain();
      const message = randomValue(types, primary);
      const domainTypes = typesForDomain(domain as any);

      const oracle = TypedDataEncoder.hash(domain, types, message);
      const d = encodeTypedDomain({ domain: domain as any });
      let m: string;
      try {
        m = encodeTypedMessage({ types: types as any, message });
      } catch (e) {
        throw new Error(
          `encodeTypedMessage threw on ${primary} ${JSON.stringify(types)}: ${e}`,
        );
      }
      const ns = toAbiTypes({
        domain: domain as any,
        types: types as any,
      }) as Node[];
      const sdk = await call(d, m, ns);

      const allDefs = { EIP712Domain: domainTypes, ...types } as Types;
      const domVal = leanValue(allDefs, "EIP712Domain", domain);
      const msgVal = leanValue(allDefs, primary, message);
      const specLine = `es ${leanDefs(allDefs)} ${primary} ${domVal} ${msgVal}`;
      const layLine = `lay ${leanDefs(allDefs)} ${primary} ${leanTypes(ns)}`;

      const inputs: [string, string, Node[]][] = [[d, m, ns]];
      for (let j = 0; j < MUTATIONS; j++) {
        const r = int(4);
        inputs.push([
          r === 0 ? mutateBytes(d) : d,
          r === 1 || r === 3 ? mutateBytes(m) : m,
          r === 2 ? mutateTypes(ns) : ns,
        ]);
      }
      const contract: string[] = [];
      for (const [dd, mm, nn] of inputs) contract.push(await call(dd, mm, nn));
      mutated += inputs.length - 1;
      mutatedOk += contract.slice(1).filter((x) => x !== "revert").length;
      const encLines = inputs.map(
        ([dd, mm, nn]) => `eh ${dd} ${mm} ${leanTypes(nn)}`,
      );

      cases.push({
        oracle,
        sdk,
        domainTypes,
        types,
        primary,
        specLine,
        layLine,
        encLines,
        contract,
      });
    }

    const lines = cases.flatMap((c) => [c.specLine, c.layLine, ...c.encLines]);
    const out = lean(lines);
    let i = 0;
    const failures: string[] = [];
    for (const c of cases) {
      const [specDigest, domHash, primHash] = out[i++].split(" ");
      const label = `${c.primary} ${JSON.stringify(c.types)}`;
      const lay = out[i++];
      if (lay !== "ok")
        failures.push(`toAbiTypes is not the type tree: ${lay}: ${label}`);
      if (c.sdk !== c.oracle)
        failures.push(`SDK+contract ${c.sdk} != ethers ${c.oracle}: ${label}`);
      if (specDigest !== c.oracle)
        failures.push(
          `Lean spec ${specDigest} != ethers ${c.oracle}: ${label}`,
        );
      const sdkPrim = hashType({
        types: c.types as any,
        type: c.primary,
      }).typeHash;
      if (sdkPrim !== primHash)
        failures.push(`SDK hashType ${sdkPrim} != Lean ${primHash}: ${label}`);
      const sdkDom = hashType({
        types: { EIP712Domain: c.domainTypes } as any,
        type: "EIP712Domain",
      }).typeHash;
      if (sdkDom !== domHash)
        failures.push(`SDK domain hashType ${sdkDom} != Lean ${domHash}`);
      for (let j = 0; j < c.encLines.length; j++) {
        const model = out[i++];
        if (model !== c.contract[j]) {
          failures.push(
            `encoder: Lean ${model} != contract ${c.contract[j]}: ${c.encLines[j]}`,
          );
        }
      }
    }
    console.log(
      `      ${cases.length} typed messages, ${mutated} mutated inputs (${mutatedOk} accepted by the contract)`,
    );
    if (failures.length > 0 && process.env.EIP712_DUMP) {
      writeFileSync(process.env.EIP712_DUMP, failures.join("\n") + "\n");
    }
    expect(failures.slice(0, 5)).to.deep.equal([]);
  });
  it("allowSignTypedMessage permissions follow the type tree and admit exactly the scoped messages", () => {
    // The SDK's authoring helpers do not load under Hardhat's module loader
    // (an import cycle), so this part runs in its own tsx process.
    const res = spawnSync(TSX, [path.resolve(here, "../../scripts/formal/eip712-permissions.ts")], {
      encoding: "utf8",
      env: {
        ...process.env,
        EIP712_CASES: String(CASES),
        EIP712_SEED: String(SEED),
      },
      maxBuffer: 1 << 30,
    });
    if (res.status !== 0) throw new Error(res.stderr || res.stdout);
    const r = JSON.parse(res.stdout.trim().split("\n").pop()!);
    console.log(
      `      ${r.checks} permission checks (${r.slices} Slices, ${r.zips} Zips), ${r.negatives} changed messages, ${r.misfitChecks} trees outside the theorem, ${r.rejected} permissions the SDK rejected`,
    );
    expect(r.misfitChecks).to.be.greaterThan(0);
    expect(r.slices).to.be.greaterThan(0);
    expect(r.zips).to.be.greaterThan(0);
    expect(r.rejectedExamples).to.deep.equal([]);
    expect(r.failures).to.deep.equal([]);
  });
});
