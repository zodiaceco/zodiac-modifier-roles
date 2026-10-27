import { Interface } from "ethers"

import { Allowance, Condition, Operator } from "./types"

const U128_MAX = (1n << 128n) - 1n

/**
 * The balance and timestamp an allowance has at `now`: the contract's
 * `AllowanceConsumer.accrue` (what `accruedAllowance(key)` returns). Each
 * full period since `timestamp` adds `refill`, capped at `maxRefill` (a
 * balance already at or above the cap stays), and the timestamp moves by
 * whole periods.
 */
export const accrueAllowance = (
  allowance: Pick<
    Allowance,
    "refill" | "maxRefill" | "period" | "balance" | "timestamp"
  >,
  now: bigint
): { balance: bigint; timestamp: bigint } => {
  const { refill, maxRefill, period, balance, timestamp } = allowance
  if (period === 0n || now <= timestamp) return { balance, timestamp }
  const k = (now - timestamp) / period
  if (k === 0n) return { balance, timestamp }
  const ts = timestamp + k * period
  if (balance >= maxRefill) return { balance, timestamp: ts }
  const accrued = balance + refill * k
  return { balance: accrued < maxRefill ? accrued : maxRefill, timestamp: ts }
}

export interface AllowanceRefill {
  refill: bigint
  /** Cap at which refilling stops; 0 means no cap (`type(uint128).max`). */
  maxRefill: bigint
  /** Refill interval in seconds; 0 means no refill. */
  period: bigint
}

/**
 * Changes an allowance's refill without crediting the new refill for the
 * time before the change.
 *
 * The contract's `updateAllowance` keeps the stored balance and timestamp,
 * so at the next use the new refill also pays for every period since the
 * allowance was last touched. This instead credits the old refill up to
 * `now`, then starts the new refill and period from the accrued timestamp:
 * pass the result to `setAllowance` (`encodeSetAllowance`).
 *
 * `now` must not be later than when the call executes (use the latest block
 * time), or periods that have not yet elapsed are credited. The call sets
 * the balance outright: anything the role spends between `now` and the
 * call's execution is credited back, so plan it right before executing, or
 * when the role cannot spend.
 *
 * @param current The allowance as stored (`allowances(key)`)
 * @param next The new refill, cap and period
 * @param now The time to credit the old refill up to
 */
export const accrueThenUpdate = (
  current: Allowance,
  next: AllowanceRefill,
  now: bigint
): Allowance => {
  const { balance, timestamp } = accrueAllowance(current, now)
  return {
    key: current.key,
    balance,
    timestamp,
    refill: next.refill,
    maxRefill: next.maxRefill === 0n ? U128_MAX : next.maxRefill,
    period: next.period,
  }
}

const setAllowanceInterface = new Interface([
  "function setAllowance(bytes32 key, uint128 balance, uint128 maxRefill, uint128 refill, uint64 period, uint64 timestamp)",
])

/** Calldata for `setAllowance` with these values. */
export const encodeSetAllowance = (allowance: Allowance): `0x${string}` =>
  setAllowanceInterface.encodeFunctionData("setAllowance", [
    allowance.key,
    allowance.balance,
    allowance.maxRefill,
    allowance.refill,
    allowance.period,
    allowance.timestamp,
  ]) as `0x${string}`

/**
 * Checks that the conditions metering each allowance agree on its unit:
 *
 * - every `WithinAllowance` with a conversion uses the same balance
 *   decimals for a key (each charges in the units its own decimals define,
 *   so with 6 in one condition and 18 in another, one of them charges
 *   10^12 times too little);
 * - a key is not used both to count calls (`CallWithinAllowance`) and to
 *   meter amounts (`WithinAllowance`).
 *
 * Pass every condition that uses the allowances (allowance keys are shared
 * by all roles of a Roles modifier).
 */
export const checkAllowanceUnits = (conditions: readonly Condition[]): void => {
  const decimals = new Map<string, number>()
  const amounts = new Set<string>()
  const calls = new Set<string>()

  const visit = (c: Condition) => {
    c.children?.forEach(visit)
    const cv = c.compValue
    if (!cv || cv.length < 66) return
    const key = cv.slice(0, 66).toLowerCase()
    if (c.operator === Operator.CallWithinAllowance) {
      calls.add(key)
    } else if (c.operator === Operator.WithinAllowance) {
      amounts.add(key)
      if (cv.length >= 70) {
        const db = parseInt(cv.slice(66, 68), 16)
        const seen = decimals.get(key)
        if (seen !== undefined && seen !== db) {
          throw new Error(
            `Allowance ${key} is metered with balance decimals ${seen} and ${db}: every condition on an allowance must use the same balance decimals`
          )
        }
        decimals.set(key, db)
      }
    }
  }
  conditions.forEach(visit)

  for (const key of calls) {
    if (amounts.has(key)) {
      throw new Error(
        `Allowance ${key} is used both to count calls (CallWithinAllowance) and to meter amounts (WithinAllowance)`
      )
    }
  }
}
