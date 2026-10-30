/**
 * Differential test of the MultiSend proof (formal/MultiSend).
 *
 * Random batches, valid and mutated (operation 2, trailing bytes, wrong
 * data lengths, header edits, empty batches, random byte flips):
 *
 * 1. `MultiSendUnwrapper.unwrap` returns what the Lean transcription
 *    returns, entries or revert.
 * 2. The calls `MultiSend.multiSend` makes, delegatecalled like a Safe does
 *    (`MockDelegator`, calls recorded by `MockRecorder`), are what the Lean
 *    transcription of its loop executes.
 * 3. When the unwrapper accepts, MultiSend executes exactly the unwrapped
 *    entries with their calldata slices (`MultiSend.unwrap_exec`).
 *
 * Needs the Lean driver (`cd formal && lake build roles-model`).
 */
import { expect } from "chai";
import { network } from "hardhat";
import { existsSync, writeFileSync } from "node:fs";
import { Interface, concat, getBytes, hexlify, solidityPacked } from "ethers";
import { LEAN_BIN, lean, makeGen } from "./eip712-gen";

const CASES = Number(process.env.MULTISEND_CASES ?? 400);
const SEED = Number(process.env.MULTISEND_SEED ?? 1);

const { ethers } = await network.create();
const iface = new Interface(["function multiSend(bytes transactions)"]);

type Tx = { op: number; to: string; value: bigint; data: string };

const fmtEntry = (
  op: number | bigint,
  to: bigint,
  value: bigint,
  data: string,
) => `${op}:${to}:${value}:${hexlify(data)}`;

describe("MultiSend: unwrapper, MultiSend and Lean", function () {
  it(`MultiSend executes exactly what the unwrapper returns (${CASES} batches)`, async function () {
    if (!existsSync(LEAN_BIN)) this.skip();
    this.timeout(0);
    const { int, chance, pick, randHex } = makeGen(SEED);

    const unwrapper = await (
      await ethers.getContractFactory("MultiSendUnwrapper")
    ).deploy();
    const multiSend = await (
      await ethers.getContractFactory("MultiSend")
    ).deploy();
    const recorders = await Promise.all(
      [0, 1, 2].map(async () =>
        (await ethers.getContractFactory("MockRecorder")).deploy(),
      ),
    );
    const recorderAddrs = await Promise.all(
      recorders.map((r) => r.getAddress()),
    );
    const recorderSet = new Set(recorderAddrs.map((a) => BigInt(a)));
    const delegator = await (
      await ethers.getContractFactory("MockDelegator")
    ).deploy();
    const delegatorAddr = await delegator.getAddress();
    const [signer] = await ethers.getSigners();
    await signer.sendTransaction({ to: delegatorAddr, value: 10n ** 18n });
    const recorderIface = recorders[0].interface;

    const encodeTx = (t: Tx) =>
      solidityPacked(
        ["uint8", "address", "uint256", "uint256", "bytes"],
        [t.op, t.to, t.value, getBytes(t.data).length, t.data],
      );
    const randTx = (): Tx => ({
      op: int(2),
      to: pick(recorderAddrs),
      value: BigInt(int(4)),
      data: randHex(int(70)),
    });

    /** A random batch's calldata and what was done to it. */
    const randCase = (): { data: string; what: string } => {
      const txs = Array.from({ length: 1 + int(4) }, randTx);
      let batch = getBytes(concat(txs.map(encodeTx)));
      let what = "valid";
      const m = int(10);
      if (m === 0) {
        // an operation other than call / delegatecall
        const t = txs[int(txs.length)];
        t.op = 2 + int(254);
        batch = getBytes(concat(txs.map(encodeTx)));
        what = "operation";
      } else if (m === 1) {
        batch = getBytes(concat([batch, randHex(1 + int(100))]));
        what = "trailing bytes";
      } else if (m === 2) {
        // one entry's data length off by some bytes
        const k = int(txs.length);
        const at =
          txs
            .slice(0, k)
            .reduce((s, t) => s + 85 + getBytes(t.data).length, 0) + 53;
        const len =
          BigInt(getBytes(txs[k].data).length) +
          BigInt(int(2) ? 1 + int(40) : -(1 + int(40)));
        if (len >= 0n)
          batch.set(getBytes(solidityPacked(["uint256"], [len])), at);
        what = "data length";
      } else if (m === 3) {
        batch = new Uint8Array();
        what = "empty";
      }
      let data = getBytes(iface.encodeFunctionData("multiSend", [batch]));
      if (m === 4) {
        data = data.slice();
        data[4 + 31] = pick([0x00, 0x40, 0x21]); // offset word
        what = "offset";
      } else if (m === 5) {
        data = data.slice();
        data[36 + 31] ^= 1 + int(255); // length word
        what = "length word";
      } else if (m === 6) {
        data = chance(0.5)
          ? data.slice(0, data.length - 1 - int(31))
          : getBytes(concat([data, randHex(1 + int(40))]));
        what = "calldata size";
      } else if (m === 7) {
        // non-zero padding after the batch
        data = data.slice();
        if (68 + batch.length < data.length)
          data[data.length - 1] = 1 + int(255);
        what = "padding";
      } else if (m === 8) {
        data = data.slice();
        const i = int(data.length);
        data[i] ^= 1 + int(255);
        what = `byte ${i}`;
      }
      return { data: hexlify(data), what };
    };

    const cases = Array.from({ length: CASES }, randCase);
    const lines = cases.flatMap((c) => [`uw ${c.data}`, `ms ${c.data}`]);
    if (process.env.MULTISEND_LINES)
      writeFileSync(process.env.MULTISEND_LINES, lines.join("\n") + "\n");
    const out = lean(lines);

    const failures: string[] = [];
    let accepted = 0;
    let executed = 0;
    let skipped = 0;
    for (let k = 0; k < cases.length; k++) {
      const { data, what } = cases[k];
      const leanUw = out[2 * k];
      const leanMs = out[2 * k + 1];

      // 1. the unwrapper
      let sol: string;
      try {
        const us = await unwrapper.unwrap(ethers.ZeroAddress, 0, data, 1);
        sol = us
          .map(
            (u: any) =>
              `${u.operation}:${BigInt(u.to)}:${u.value}:${u.dataLocation}:${u.dataSize}`,
          )
          .join(";");
      } catch {
        sol = "revert";
      }
      if (sol !== leanUw)
        failures.push(
          `unwrap (${what}): contract ${sol}, Lean ${leanUw}: ${data}`,
        );

      // 2. what MultiSend executes
      if (leanMs === "decode" || leanMs === "junk") {
        skipped++;
      } else {
        let got: string;
        try {
          const tx = await delegator.run(await multiSend.getAddress(), data);
          const rc = await tx.wait();
          got =
            rc!.logs
              .map((l) => recorderIface.parseLog(l))
              .filter((e) => e?.name === "Called")
              .map((e) => {
                const op = e!.args.context === delegatorAddr ? 1 : 0;
                return fmtEntry(
                  op,
                  BigInt(e!.args.self),
                  op ? 0n : e!.args.value,
                  e!.args.data,
                );
              })
              .join(";") || "-";
        } catch {
          got = "revert";
        }
        // calls to addresses other than the recorders leave no log
        const want =
          leanMs === "revert" || leanMs === "-"
            ? leanMs
            : leanMs
                .split(";")
                .map((s) => s.split(":"))
                .filter(([, to]) => recorderSet.has(BigInt(to)))
                .map(([op, to, value, d]) =>
                  fmtEntry(
                    Number(op),
                    BigInt(to),
                    op === "1" ? 0n : BigInt(value),
                    d,
                  ),
                )
                .join(";") || "-";
        // a call sending more than the delegator holds fails, and MultiSend
        // reverts (the model leaves failing calls out: they only remove
        // executions)
        const overspends =
          leanMs !== "revert" &&
          leanMs !== "-" &&
          leanMs.split(";").some((s) => {
            const [op, , value] = s.split(":");
            return op === "0" && BigInt(value) > 10n ** 17n;
          });
        if (got === "revert" && overspends) skipped++;
        else if (got !== want)
          failures.push(
            `multiSend (${what}): EVM ${got}, Lean ${want}: ${data}`,
          );
        else executed++;
      }

      // 3. accepted batches: MultiSend executes the unwrapped entries
      if (leanUw !== "revert") {
        accepted++;
        const bytes = getBytes(data);
        const viaUnwrap = leanUw
          .split(";")
          .map((s) => s.split(":").map(BigInt))
          .map(([op, to, value, loc, size]) =>
            fmtEntry(
              op,
              to,
              value,
              hexlify(bytes.slice(Number(loc), Number(loc + size))),
            ),
          )
          .join(";");
        if (leanMs !== viaUnwrap)
          failures.push(
            `accepted (${what}) but MultiSend executes ${leanMs}, unwrapper ${viaUnwrap}`,
          );
      }
    }
    console.log(
      `      ${CASES} batches: ${accepted} accepted by the unwrapper, ${executed} executions compared, ${skipped} skipped (not a multiSend call, memory-dependent, or a call that cannot pay)`,
    );
    expect(failures.slice(0, 5)).to.deep.equal([]);
    expect(accepted).to.be.greaterThan(0);
  });
});
