import {
  BigNumberish,
  ParamType,
  getAddress,
  hexlify,
  solidityPacked,
} from "ethers"
import { Operator, Encoding } from "../../../types"

import { abiEncode } from "../../../abiEncode"
import { encodeKey } from "../../../keys"

import { ConditionFunction } from "../types"

/** The contract rejects decimals above this (`AllowanceDecimalsExceedMax`). */
export const MAX_ALLOWANCE_DECIMALS = 27

export interface AllowanceConversion {
  /** Decimals of the allowance balance. Every condition on the allowance
   *  must use the same value. */
  balanceDecimals: number
  /** Decimals of the metered parameter. */
  inputDecimals: number
  /** `IPricing` adapter whose `getPrice(params)` returns the balance units
   *  per input unit, with 18 decimals. Omitted: price 1. */
  priceAdapter?: `0x${string}`
  /** Extra bytes passed to `getPrice`. */
  adapterParams?: string
}

/**
 * Meters the parameter against an allowance.
 *
 * Without a conversion, the parameter is in balance units. With one, the
 * amount is converted to balance units (the decimals, and the adapter's
 * price), rounded up.
 *
 * @param allowanceKey The allowance's key, as a label or already encoded
 * @param conversion Balance and input decimals, and an optional price adapter
 */
export const withinAllowance =
  (
    allowanceKey: string,
    conversion?: AllowanceConversion
  ): ConditionFunction<BigNumberish> =>
  (abiType: ParamType) => {
    const type = ParamType.from(abiType)
    if (!type.type.startsWith("uint")) {
      throw new Error("`withinAllowance` is only supported for uint params")
    }
    return {
      paramType: Encoding.Static,
      operator: Operator.WithinAllowance,
      compValue: conversion
        ? encodeAllowanceConversion(encodeKey(allowanceKey), conversion)
        : abiEncode(["bytes32"], [encodeKey(allowanceKey)]),
    }
  }

/** The WithinAllowance compValue: key, balance decimals, input decimals,
 *  and the optional adapter with its params. */
export const encodeAllowanceConversion = (
  key: `0x${string}`,
  {
    balanceDecimals,
    inputDecimals,
    priceAdapter,
    adapterParams,
  }: AllowanceConversion
): `0x${string}` => {
  for (const [name, d] of [
    ["balanceDecimals", balanceDecimals],
    ["inputDecimals", inputDecimals],
  ] as const) {
    if (!Number.isInteger(d) || d < 0 || d > MAX_ALLOWANCE_DECIMALS) {
      throw new Error(
        `\`${name}\` must be an integer from 0 to ${MAX_ALLOWANCE_DECIMALS}`
      )
    }
  }
  if (adapterParams !== undefined && priceAdapter === undefined) {
    throw new Error("`adapterParams` require a `priceAdapter`")
  }
  if (priceAdapter === undefined) {
    return solidityPacked(
      ["bytes32", "uint8", "uint8"],
      [key, balanceDecimals, inputDecimals]
    ) as `0x${string}`
  }
  return solidityPacked(
    ["bytes32", "uint8", "uint8", "address", "bytes"],
    [
      key,
      balanceDecimals,
      inputDecimals,
      getAddress(priceAdapter),
      hexlify(adapterParams ?? "0x"),
    ]
  ) as `0x${string}`
}
