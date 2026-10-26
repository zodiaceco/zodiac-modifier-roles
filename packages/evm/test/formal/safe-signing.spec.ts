/**
 * Differential test of `uintToString` (formal/SafeSigning): the contract,
 * the Lean transcription (proven equal to the decimal, `uintToString_eq`)
 * and JavaScript's decimal agree on random uint256 values. The keys
 * `SignTypedMessageLib` stores and what the Safe's handler accepts are
 * tested against a real Safe in packages/integration-tests
 * (test/eip712/safe-signing-lean.spec.ts).
 */
import { expect } from "chai";
import { network } from "hardhat";
import { existsSync } from "node:fs";
import { LEAN_BIN, lean, makeGen } from "./eip712-gen";

const CASES = Number(process.env.U2S_CASES ?? 500);
const { ethers } = await network.create();

describe("uintToString: contract, Lean and decimal", function () {
  it(`agree on ${CASES} random uint256 values`, async function () {
    if (!existsSync(LEAN_BIN)) this.skip();
    const { int, randHex } = makeGen(7);
    const mock = await (
      await ethers.getContractFactory("MockUintToString")
    ).deploy();
    const max = (1n << 256n) - 1n;
    const values = [0n, 1n, 9n, 10n, 99n, 100n, 101n, max, max - 1n];
    for (let k = 1; k < 78; k++)
      values.push(10n ** BigInt(k) - 1n, 10n ** BigInt(k));
    while (values.length < CASES) {
      const bytes = 1 + int(32);
      values.push(BigInt(randHex(bytes)) >> BigInt(int(8)));
    }
    const out = lean(values.map((v) => `u2s ${v}`));
    const failures: string[] = [];
    for (let i = 0; i < values.length; i++) {
      const sol = await mock.asString(values[i]);
      const want = values[i].toString();
      if (sol !== want || out[i] !== want)
        failures.push(`${want}: contract ${sol}, Lean ${out[i]}`);
    }
    console.log(`      ${values.length} values`);
    expect(failures.slice(0, 5)).to.deep.equal([]);
  });
});
