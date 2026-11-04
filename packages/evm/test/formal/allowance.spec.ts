/**
 * Differential test of the allowance proofs (formal/Allowance).
 *
 * Random allowances (refill, cap, period, stored timestamp in the past or
 * future) metered by `fn(uint256 a, uint256 b)` with a WithinAllowance (or
 * Pass) on each parameter: raw amounts, amounts with balance and input
 * decimals, and priced amounts through MockPricing adapters (zero prices
 * included). Transactions at random block times, with amounts at the exact
 * limit, one above, huge (overflow) or random.
 *
 * Some steps change the refill instead: the SDK's `accrueThenUpdate` plans
 * the `setAllowance` call, which the owner executes at that time.
 *
 * For every step, the outcome (stored, AllowanceExceeded, zero price,
 * panic) and the stored balance and timestamp after it are what the Lean
 * transcription (`Allowance.tx`, `Allowance.accrueThenUpdate`) gives, and
 * before it the SDK's `accrueAllowance` is the contract's
 * `accruedAllowance`.
 *
 * Needs the Lean driver (`cd formal && lake build roles-model`).
 */
import { expect } from "chai";
import { network } from "hardhat";
import { existsSync } from "node:fs";
import { Interface, hexlify, randomBytes, solidityPacked } from "ethers";
import { LEAN_BIN, lean, makeGen } from "./eip712-gen";
import { createSetup } from "../setup";
import { ConditionViolationStatus, Encoding, Operator } from "../utils";
import {
  accrueAllowance,
  accrueThenUpdate,
} from "../../../sdk/src/main/allowance.js";

const SCENARIOS = Number(process.env.ALLOWANCE_SCENARIOS ?? 200);
const TXS = Number(process.env.ALLOWANCE_TXS ?? 10);
const SEED = Number(process.env.ALLOWANCE_SEED ?? 1);

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { setupTwoParams } = createSetup(connection);

const U128 = (1n << 128n) - 1n;
const U256 = (1n << 256n) - 1n;
const E18 = 10n ** 18n;

type Meter =
  | { kind: "pass" }
  | { kind: "raw" }
  | { kind: "priced"; db: number; di: number; price: bigint; adapter?: string };

describe("Allowances: Roles against Lean", function () {
  after(async () => {
    await connection.close();
  });

  it(`stores what the Lean model stores (${SCENARIOS} allowances × ${TXS} transactions)`, async function () {
    if (!existsSync(LEAN_BIN)) this.skip();
    this.timeout(0);
    const { int, chance, pick, randHex } = makeGen(SEED);
    const randBig = (bits: number) =>
      BigInt(randHex(Math.ceil(bits / 8))) % (1n << BigInt(bits));
    const { roles, owner, member, testContractAddress, fn, allowFunction } =
      await setupTwoParams();
    const fnIface = new Interface([fn]);
    const invoke = (a: bigint, b: bigint) =>
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          fnIface.encodeFunctionData(fn, [a, b]),
          0,
          { gasLimit: 5_000_000 },
        );
    const rolesIface: Interface = roles.interface;

    const pricing = await ethers.getContractFactory("MockPricing");
    const randPrice = () =>
      pick([
        E18,
        2n * E18,
        E18 / 3n,
        1n,
        0n,
        randBig(64),
        randBig(100),
        10n ** 30n,
        U256 >> BigInt(int(200)),
      ]);
    const randAmount = () =>
      pick([0n, 1n, randBig(8), randBig(32), randBig(64), randBig(128), U128]);

    const failures: string[] = [];
    const counts: Record<string, number> = {};

    for (let sc = 0; sc < SCENARIOS; sc++) {
      const key = hexlify(randomBytes(32));

      // ---- the allowance
      const latest = BigInt(await networkHelpers.time.latest());
      const period = pick([0n, 1n, 7n, 100n, 3600n, BigInt(int(1000))]);
      const tsChoice = int(3);
      const timestamp =
        tsChoice === 0
          ? 0n // Setup stores block.timestamp
          : tsChoice === 1
            ? latest - BigInt(int(5000))
            : latest + BigInt(int(500));
      await roles
        .connect(owner)
        .setAllowance(
          key,
          randAmount(),
          pick([0n, randAmount(), 1n]),
          randAmount(),
          period,
          timestamp,
        );
      const stored = await roles.allowances(key);
      let cfg = {
        refill: stored.refill,
        maxRefill: stored.maxRefill,
        period: stored.period,
      };
      let state = { balance: stored.balance, timestamp: stored.timestamp };
      const head = `al ${cfg.refill} ${cfg.maxRefill} ${cfg.period} ${state.balance} ${state.timestamp}`;

      // ---- how each parameter is metered
      const randMeter = async (): Promise<Meter> => {
        const k = int(4);
        if (k === 0) return { kind: "raw" };
        const db = int(28);
        const di = int(28);
        if (k === 1) return { kind: "priced", db, di, price: E18 };
        const price = randPrice();
        const adapter = await (await pricing.deploy(price)).getAddress();
        return { kind: "priced", db, di, price, adapter };
      };
      const meters: Meter[] = [
        await randMeter(),
        chance(0.4) ? { kind: "pass" } : await randMeter(),
      ];
      const node = (m: Meter) =>
        m.kind === "pass"
          ? {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.Pass,
              compValue: "0x",
            }
          : {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.WithinAllowance,
              compValue:
                m.kind === "raw"
                  ? key
                  : m.adapter
                    ? solidityPacked(
                        ["bytes32", "uint8", "uint8", "address"],
                        [key, m.db, m.di, m.adapter],
                      )
                    : solidityPacked(
                        ["bytes32", "uint8", "uint8"],
                        [key, m.db, m.di],
                      ),
            };
      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        node(meters[0]),
        node(meters[1]),
      ]);

      // ---- transactions
      const spendOf = (m: Meter, v: bigint) =>
        m.kind === "raw"
          ? `r.${v}`
          : m.kind === "priced"
            ? `p.${v}.${m.price}.${m.db}.${m.di}`
            : "";
      const txs: string[] = [];
      const got: string[] = [];
      let now = BigInt(await networkHelpers.time.latest());
      for (let t = 0; t < TXS; t++) {
        const gap = pick([
          1n,
          BigInt(1 + int(10)),
          cfg.period === 0n ? 1n : cfg.period,
          cfg.period * BigInt(1 + int(5)) + BigInt(int(3)),
          BigInt(int(20000)),
        ]);
        // the SDK's accrual is the contract's, at the latest block
        const latestTs = BigInt(await networkHelpers.time.latest());
        const view = await roles.accruedAllowance(key);
        const sdk = accrueAllowance({ ...cfg, ...state }, latestTs);
        if (view.balance !== sdk.balance || view.timestamp !== sdk.timestamp)
          failures.push(
            `accruedAllowance ${view.balance}:${view.timestamp}, SDK ${sdk.balance}:${sdk.timestamp} at ${latestTs}: ${head} ${txs.join(" ")}`,
          );
        counts.accrualChecks = (counts.accrualChecks ?? 0) + 1;

        now += gap > 0n ? gap : 1n;

        if (t > 0 && chance(0.15)) {
          // change the refill through the SDK
          const planned = accrueThenUpdate(
            { key: key as `0x${string}`, ...cfg, ...state },
            {
              refill: randAmount(),
              maxRefill: pick([0n, randAmount(), 1n]),
              period: pick([0n, 1n, 7n, 100n, BigInt(1 + int(1000))]),
            },
            now,
          );
          await networkHelpers.time.setNextBlockTimestamp(now);
          await (
            await roles
              .connect(owner)
              .setAllowance(
                key,
                planned.balance,
                planned.maxRefill,
                planned.refill,
                planned.period,
                planned.timestamp,
              )
          ).wait();
          const s = await roles.allowances(key);
          cfg = { refill: s.refill, maxRefill: s.maxRefill, period: s.period };
          state = { balance: s.balance, timestamp: s.timestamp };
          if (
            cfg.refill !== planned.refill ||
            cfg.maxRefill !== planned.maxRefill ||
            cfg.period !== planned.period
          )
            failures.push(`setAllowance stored other parameters than planned`);
          txs.push(
            `${now}/u.${planned.refill}.${planned.maxRefill}.${planned.period}`,
          );
          got.push(`ok:${s.balance}:${s.timestamp}`);
          counts.updates = (counts.updates ?? 0) + 1;
          continue;
        }
        // what is left, to aim at the limit
        const left = accrueAllowance({ ...cfg, ...state }, now).balance;
        const values = meters.map((m, i) => {
          if (m.kind === "pass") return BigInt(int(1000));
          const share = i === 0 && meters[1].kind !== "pass" ? left / 2n : left;
          let limit = share;
          if (m.kind === "priced") {
            limit =
              m.price === 0n
                ? share
                : (share * E18 * 10n ** BigInt(m.di)) /
                  (m.price * 10n ** BigInt(m.db));
          }
          const v = pick([
            limit,
            limit + 1n,
            limit > 0n ? limit - 1n : 0n,
            0n,
            U256,
            randAmount(),
          ]);
          return v > U256 ? U256 : v;
        });
        const spends = meters
          .map((m, i) => spendOf(m, values[i]))
          .filter((x) => x !== "");
        txs.push(`${now}/${spends.length ? spends.join(",") : "-"}`);

        await networkHelpers.time.setNextBlockTimestamp(now);
        let outcome: string;
        try {
          await (await invoke(values[0], values[1])).wait();
          const s = await roles.allowances(key);
          if (s.timestamp > state.timestamp)
            counts.refilled = (counts.refilled ?? 0) + 1;
          if (s.balance === 0n && state.balance > 0n)
            counts.drained = (counts.drained ?? 0) + 1;
          state = { balance: s.balance, timestamp: s.timestamp };
          outcome = `ok:${s.balance}:${s.timestamp}`;
        } catch (e: any) {
          outcome = classify(rolesIface, e);
          const blockTs = BigInt(await networkHelpers.time.latest());
          if (blockTs !== now) {
            // the failing transaction was not mined: mine the block ourselves
            await networkHelpers.mine();
          }
          const s = await roles.allowances(key);
          if (s.balance !== state.balance || s.timestamp !== state.timestamp)
            failures.push(
              `failed tx changed the allowance: ${head} ${txs.join(" ")}`,
            );
        }
        got.push(outcome);
        counts[outcome.split(":")[0]] =
          (counts[outcome.split(":")[0]] ?? 0) + 1;
      }
      const want = lean([`${head} ${txs.join(" ")}`])[0].split(" ");
      for (let t = 0; t < TXS; t++) {
        if (got[t] !== want[t])
          failures.push(
            `tx ${t}: Roles ${got[t]}, Lean ${want[t]}: ${head} ${txs.slice(0, t + 1).join(" ")} (meters ${JSON.stringify(meters, (_, v) => (typeof v === "bigint" ? v.toString() : v))})`,
          );
      }
    }
    console.log(`      outcomes: ${JSON.stringify(counts)}`);
    expect(failures.slice(0, 5)).to.deep.equal([]);
  });
});

function classify(iface: Interface, e: any): string {
  const data: string | undefined =
    e?.data ?? e?.error?.data ?? e?.info?.error?.data ?? e?.receipt?.revertData;
  if (typeof data === "string" && data.startsWith("0x4e487b71")) return "panic";
  if (typeof data === "string" && data.length > 2) {
    try {
      const err = iface.parseError(data);
      if (err?.name === "ConditionViolation") {
        const status = Number(err.args[0]);
        if (status === ConditionViolationStatus.AllowanceExceeded)
          return "exceeded";
        if (status === ConditionViolationStatus.PricingAdapterZeroPrice)
          return "deny";
        return `violation-${status}`;
      }
      return `error-${err?.name}`;
    } catch {
      return `unknown-${data.slice(0, 10)}`;
    }
  }
  return `no-data: ${String(e?.message ?? e).slice(0, 120)}`;
}
