# Allowances

What a role can spend from an allowance over time: the refill
(`AllowanceConsumer.accrue`), the conversion of a spend into balance units
with decimals and a price adapter (`WithinAllowanceChecker._scaleInput`),
consumption, and what `Settlement._persist` stores after each transaction.

```
cd packages/evm/formal
lake build Allowance
```

## The model

`Basic.lean` transcribes the contract:

- `accrue`: `k = (now - timestamp) / period` full periods add `refill` each,
  capped at `maxRefill` (a balance already at or above the cap stays), and
  the timestamp moves by `k` periods.
- `charge`: a raw amount (a 32-byte compValue, `CallWithinAllowance`, a
  custom checker's consumption) is charged as is; a priced amount `v` with
  input decimals `di`, balance decimals `db` and price `p` (18 decimals;
  `10^18` without an adapter) is charged
  `ceilDiv(v·10^(P-di)·p, 10^(P-db)·10^18)` with `P = max db di`. A zero
  price is a violation, and an overflow in the checked arithmetic is a
  revert.
- `tx`: the first spend accrues the allowance; each spend is consumed if it
  fits what is left; the transaction stores the accrued balance minus what it
  consumed, and the accrued timestamp. A transaction that fails stores
  nothing. `run` chains transactions.

## What is proven

| Theorem (`Agree.lean`)            | Statement                                                                                                                                                                                                                       |
| --------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `scale_eq`                        | Scaling to the higher precision loses nothing: the charge is `⌈v·p·10^db / (10^18·10^di)⌉`, the value rounded up once, whatever the two decimals.                                                                               |
| `charge_fits_iff`                 | A priced spend fits what is left, `R`, exactly when its value does: `v·p·10^db ≤ R·10^18·10^di`. Rounding never rejects a spend whose value fits.                                                                               |
| `charge_covers`, `charge_pos`     | Each charge is at least the spend's value, less than one balance unit above it, and never 0 for a nonzero amount.                                                                                                              |
| `charged_covers`                  | **Rounding does not accumulate in the role's favour.** Over any spends, with any prices and input decimals, the total charged is at least the total value, and exceeds it by less than one balance unit per spend.               |
| `accrue_eq`                       | Closed form of `accrue`.                                                                                                                                                                                                        |
| `accrue_accrue`                   | Accruing at `t1` and then at `t2` is the same as accruing at `t2`: when transactions happen, or whether any happen in between, does not change the balance.                                                                      |
| `accrue_cap`                      | Refills never raise the balance above `max(balance, maxRefill)`.                                                                                                                                                                |
| `accrue_bounds`                   | With the storage word sizes (`uint128` amounts, `uint64` times), the elapsed periods times the period fit `uint64`, `balance + refill·k` fits `uint256`, and the results fit the storage words.                                   |
| `spending_limit`                  | **Spending limit.** Over any transactions up to time `T`, the role is charged at most the stored balance plus `refill` for each full period from the stored timestamp to `T`.                                                     |
| `value_limit`                     | The same bound on the **value** spent, in balance units, across any mix of prices and decimals (`spending_limit` with `charged_covers`).                                                                                         |
| `accrueThenUpdate_same`           | The SDK's `accrueThenUpdate` changes nothing when the parameters stay: later balances are those of the untouched allowance.                                                                                                     |
| `update_limit`                    | **No retroactive refill through the SDK.** For transactions under the old refill up to `now`, `accrueThenUpdate` at `now`, then transactions under the new refill: the role is charged at most the starting balance, plus the old refill for the periods up to `now`, plus the new refill for the periods after the update. |
| `update_retroactive`              | `updateAllowance` keeps balance and timestamp without accruing first. So a new refill also pays for the periods since the last accrual: an allowance with no refill, untouched for ten periods, gets ten periods of the new refill at once. |

## SDK helpers

- `accrueThenUpdate(current, { refill, maxRefill, period }, now)` (with
  `encodeSetAllowance`): changes the refill without the retroactive credit
  of `updateAllowance`. It credits the old refill up to `now` and passes the
  accrued balance and timestamp to `setAllowance`. `setAllowance` sets the
  balance outright, so anything the role spends between `now` and the call's
  execution is credited back. Plan it right before executing, and never with
  a `now` later than the execution.
- `accrueAllowance`: the contract's `accrue`.
- `withinAllowance(key, { balanceDecimals, inputDecimals, priceAdapter?, adapterParams? })`:
  encodes the conversion and rejects decimals the contract rejects.
- `checkAllowanceUnits` (run by `targetIntegrity`): rejects an allowance that
  conditions meter with different balance decimals, or that is used both to
  count calls and to meter amounts.

The value in `value_limit` is in units of the allowance balance, as each
condition's `db` and price define it. The proofs take each condition's
decimals and price as given. `checkAllowanceUnits` checks that the conditions
on an allowance agree on `db`. Nothing checks that the decimals match the
tokens.

## Tests

`test/formal/allowance.spec.ts` runs random allowances through `Roles` itself:

- Configurations: refill, cap and period; a stored timestamp in the past, in
  the future, or set from the current block.
- Metering: `fn(uint256, uint256)` with a `WithinAllowance` or `Pass` on each
  parameter. A metered parameter is either a raw amount, an amount with
  decimals, or an amount priced through `MockPricing` adapters (including
  zero and huge prices).
- Transactions run at random block times. Amounts are at the exact limit,
  one above, one below, zero, `2^256 - 1`, or random.

About one step in seven changes the refill instead: `accrueThenUpdate`
from the SDK plans the call, and the owner executes it at that block time.

For every step, the test compares the outcome and the stored balance and
timestamp with `Allowance.tx` and `Allowance.accrueThenUpdate`. Outcomes are:
stored, `AllowanceExceeded`, zero price, or panic. Before each step, it also
checks the SDK's `accrueAllowance` against the contract's
`accruedAllowance`. Results:

- Before the update steps were added: six seeds, 13,000 transactions, 0
  differences.
- With them: three seeds, 6,000 steps including 810 updates, and 6,000
  accrual checks, 0 differences.

## Not covered

- Within one transaction, which spends count: proven in
  [`EndToEnd`](../EndToEnd/README.md#batches-every-executed-transaction-passed-its-permission).
  A failed branch's consumption is discarded (`evalC_steps`). The list keeps
  one entry per key (`steps_spec`), so `_persist` stores one `tx` per
  allowance, for a batch too (`authorize_persist`). `executions_limit` is
  `spending_limit` over executions through Roles; executions never
  interleave (tested, see
  [attribution and reentrancy](../EndToEnd/README.md#attribution-and-reentrancy)),
  so it covers on-chain histories in which the owner does not change
  allowances during an execution.
- Price adapters themselves. A price is whatever the adapter returns, and a
  manipulable or stale price makes the value wrong. Adapters are chosen by
  the owner.
- Owner calls other than `accrueThenUpdate` between transactions. A
  theorem's starting state is whatever the owner set last
  (`update_retroactive` shows what a plain `updateAllowance` does).
- Spends between planning `accrueThenUpdate` and executing it (see above).
