import { describe, expect, it } from "vitest"
import { Interface } from "ethers"

import { rolesAbi } from "./abi"
import {
  accrueAllowance,
  accrueThenUpdate,
  checkAllowanceUnits,
  encodeSetAllowance,
} from "./allowance"
import { encodeAllowanceConversion } from "./target/authoring/c/allowance"
import { Allowance, Condition, Encoding, Operator } from "./types"

const key = `0x${"11".repeat(32)}` as const
const other = `0x${"22".repeat(32)}` as const
const U128_MAX = (1n << 128n) - 1n

const base: Allowance = {
  key,
  refill: 0n,
  maxRefill: U128_MAX,
  period: 100n,
  balance: 0n,
  timestamp: 1000n,
}

describe("accrueAllowance", () => {
  it("credits full periods only, moving the timestamp by whole periods", () => {
    const a = { ...base, refill: 5n }
    expect(accrueAllowance(a, 1099n)).toEqual({ balance: 0n, timestamp: 1000n })
    expect(accrueAllowance(a, 1250n)).toEqual({
      balance: 10n,
      timestamp: 1200n,
    })
  })

  it("caps at maxRefill, and leaves a balance above the cap", () => {
    expect(
      accrueAllowance({ ...base, refill: 5n, maxRefill: 12n }, 2000n)
    ).toEqual({ balance: 12n, timestamp: 2000n })
    expect(
      accrueAllowance(
        { ...base, refill: 5n, maxRefill: 12n, balance: 50n },
        2000n
      )
    ).toEqual({ balance: 50n, timestamp: 2000n })
  })

  it("credits nothing without a period, or before the stored timestamp", () => {
    expect(accrueAllowance({ ...base, refill: 5n, period: 0n }, 9999n)).toEqual(
      {
        balance: 0n,
        timestamp: 1000n,
      }
    )
    expect(accrueAllowance({ ...base, refill: 5n }, 500n)).toEqual({
      balance: 0n,
      timestamp: 1000n,
    })
  })
})

describe("accrueThenUpdate", () => {
  it("credits the old refill before the new one starts", () => {
    // untouched for ten periods without refill: the new refill pays nothing for them
    const next = accrueThenUpdate(
      base,
      { refill: 5n, maxRefill: 0n, period: 100n },
      2000n
    )
    expect(next).toEqual({
      key,
      balance: 0n,
      timestamp: 2000n,
      refill: 5n,
      maxRefill: U128_MAX,
      period: 100n,
    })
    expect(accrueAllowance(next, 2000n).balance).toBe(0n)
    expect(accrueAllowance(next, 2100n).balance).toBe(5n)
  })

  it("keeps what the old refill already earned", () => {
    const next = accrueThenUpdate(
      { ...base, refill: 7n },
      { refill: 1n, maxRefill: 0n, period: 10n },
      1350n
    )
    expect(next.balance).toBe(21n)
    expect(next.timestamp).toBe(1300n)
  })

  it("encodes to setAllowance", () => {
    const next = accrueThenUpdate(
      base,
      { refill: 1n, maxRefill: 9n, period: 3n },
      1000n
    )
    const decoded = new Interface(rolesAbi).decodeFunctionData(
      "setAllowance",
      encodeSetAllowance(next)
    )
    expect([...decoded]).toEqual([key, 0n, 9n, 1n, 3n, 1000n])
  })
})

const wa = (compValue: `0x${string}`): Condition => ({
  paramType: Encoding.Static,
  operator: Operator.WithinAllowance,
  compValue,
})
const tree = (...children: Condition[]): Condition => ({
  paramType: Encoding.AbiEncoded,
  operator: Operator.Matches,
  children,
})
const conv = (
  k: `0x${string}`,
  balanceDecimals: number,
  inputDecimals: number
) => encodeAllowanceConversion(k, { balanceDecimals, inputDecimals })

describe("checkAllowanceUnits", () => {
  it("accepts conditions that agree on the balance decimals", () => {
    expect(() =>
      checkAllowanceUnits([
        tree(wa(conv(key, 6, 18)), wa(key)),
        tree(wa(conv(key, 6, 6)), wa(conv(other, 18, 6))),
      ])
    ).not.toThrow()
  })

  it("rejects one allowance metered with two balance decimals", () => {
    expect(() =>
      checkAllowanceUnits([
        tree(wa(conv(key, 6, 18))),
        tree(wa(conv(key, 18, 18))),
      ])
    ).toThrow("balance decimals 6 and 18")
  })

  it("rejects a key that both counts calls and meters amounts", () => {
    expect(() =>
      checkAllowanceUnits([
        tree(wa(key), {
          paramType: Encoding.None,
          operator: Operator.CallWithinAllowance,
          compValue: key,
        }),
      ])
    ).toThrow("count calls")
  })
})
