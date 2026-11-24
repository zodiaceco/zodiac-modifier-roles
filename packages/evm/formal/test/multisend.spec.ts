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
import assert from "node:assert/strict";
import { existsSync, writeFileSync } from "node:fs";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import {
  bytesToHex,
  concat,
  encodeFunctionData,
  encodePacked,
  hexToBytes,
  isAddressEqual,
  parseAbi,
  parseEventLogs,
  zeroAddress,
  type Address,
  type Hex,
} from "viem";
import { LEAN_BIN, lean, makeGen } from "./eip712-gen.js";

const CASES = Number(process.env.MULTISEND_CASES ?? 400);
const SEED = Number(process.env.MULTISEND_SEED ?? 1);

const connection = await network.create();
const { viem } = connection;
const multiSendAbi = parseAbi(["function multiSend(bytes transactions)"]);

type Tx = { op: number; to: Address; value: bigint; data: Hex };

const fmtEntry = (op: number | bigint, to: bigint, value: bigint, data: Hex) =>
  `${op}:${to}:${value}:${data}`;

describe("MultiSend: unwrapper, MultiSend and Lean", () => {
  after(async () => {
    await connection.close();
  });

  it(`MultiSend executes exactly what the unwrapper returns (${CASES} batches)`, async (t) => {
    if (!existsSync(LEAN_BIN)) {
      t.skip();
      return;
    }
    const { int, chance, pick, randHex } = makeGen(SEED);

    const unwrapper = await viem.deployContract("MultiSendUnwrapper");
    const multiSend = await viem.deployContract("MultiSend");
    const recorders = await Promise.all(
      [0, 1, 2].map(() => viem.deployContract("MockRecorder")),
    );
    const recorderAddrs = recorders.map((r) => r.address);
    const recorderSet = new Set(recorderAddrs.map((a) => BigInt(a)));
    const delegator = await viem.deployContract("MockDelegator");
    const [signer] = await viem.getWalletClients();
    await signer.sendTransaction({
      to: delegator.address,
      value: 10n ** 18n,
    });
    const publicClient = await viem.getPublicClient();

    const encodeTx = (tTx: Tx) =>
      encodePacked(
        ["uint8", "address", "uint256", "uint256", "bytes"],
        [
          tTx.op,
          tTx.to,
          tTx.value,
          BigInt(hexToBytes(tTx.data).length),
          tTx.data,
        ],
      );
    const randTx = (): Tx => ({
      op: int(2),
      to: pick(recorderAddrs),
      value: BigInt(int(4)),
      data: randHex(int(70)),
    });

    /** A random batch's calldata and what was done to it. */
    const randCase = (): { data: Hex; what: string } => {
      const txs = Array.from({ length: 1 + int(4) }, randTx);
      let batch = hexToBytes(concat(txs.map(encodeTx)));
      let what = "valid";
      const m = int(10);
      if (m === 0) {
        // an operation other than call / delegatecall
        const tx = txs[int(txs.length)];
        tx.op = 2 + int(254);
        batch = hexToBytes(concat(txs.map(encodeTx)));
        what = "operation";
      } else if (m === 1) {
        batch = hexToBytes(concat([bytesToHex(batch), randHex(1 + int(100))]));
        what = "trailing bytes";
      } else if (m === 2) {
        // one entry's data length off by some bytes
        const k = int(txs.length);
        const at =
          txs
            .slice(0, k)
            .reduce((s, tx) => s + 85 + hexToBytes(tx.data).length, 0) + 53;
        const len =
          BigInt(hexToBytes(txs[k].data).length) +
          BigInt(int(2) ? 1 + int(40) : -(1 + int(40)));
        if (len >= 0n)
          batch.set(hexToBytes(encodePacked(["uint256"], [len])), at);
        what = "data length";
      } else if (m === 3) {
        batch = new Uint8Array();
        what = "empty";
      }
      let data = hexToBytes(
        encodeFunctionData({
          abi: multiSendAbi,
          functionName: "multiSend",
          args: [bytesToHex(batch)],
        }),
      );
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
          : hexToBytes(concat([bytesToHex(data), randHex(1 + int(40))]));
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
      return { data: bytesToHex(data), what };
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
        const us = await unwrapper.read.unwrap([zeroAddress, 0n, data, 1]);
        sol = us
          .map(
            (u) =>
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
          const hash = await delegator.write.run([multiSend.address, data]);
          const rc = await publicClient.getTransactionReceipt({ hash });
          got =
            parseEventLogs({
              abi: recorders[0].abi,
              logs: rc.logs,
              eventName: "Called",
            })
              .map((e) => {
                const op = isAddressEqual(e.args.context, delegator.address)
                  ? 1
                  : 0;
                return fmtEntry(
                  op,
                  BigInt(e.args.self),
                  op ? 0n : e.args.value,
                  e.args.data,
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
                    d as Hex,
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
        const bytes = hexToBytes(data);
        const viaUnwrap = leanUw
          .split(";")
          .map((s) => s.split(":").map(BigInt))
          .map(([op, to, value, loc, size]) =>
            fmtEntry(
              op,
              to,
              value,
              bytesToHex(bytes.slice(Number(loc), Number(loc + size))),
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
    assert.deepEqual(failures.slice(0, 5), []);
    assert.ok(accepted > 0);
  });
});
