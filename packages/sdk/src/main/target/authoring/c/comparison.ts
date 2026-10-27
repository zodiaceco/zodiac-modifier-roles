import {
  BigNumberish,
  BytesLike,
  concat,
  getBytes,
  hexlify,
  ParamType,
  toBeHex,
} from "ethers"
import { Encoding, Operator } from "../../../types"

import { abiEncode } from "../../../abiEncode"
import { describeStructure } from "./helpers/describeStructure"
import { parameterType } from "./helpers/parameterType"

import { ConditionFunction } from "../types"

/**
 * Asserts that the value from calldata is equal to the given value
 * @param value The reference value to encode
 */
export const eq =
  (value: any): ConditionFunction<any> =>
  (abiType: ParamType) => {
    const type = ParamType.from(abiType)
    const structure = describeStructure(type)
    return {
      paramType: parameterType(type),
      operator: Operator.EqualTo,
      compValue: abiEncode([type], [value]),
      children: structure.children,
    }
  }

/**
 * Asserts that the value from calldata is equal to the avatar address configured on the Roles mod
 */
export const avatar: ConditionFunction<string> = (abiType: ParamType) => {
  const type = ParamType.from(abiType)
  const structure = describeStructure(type)
  return {
    paramType: parameterType(type),
    operator: Operator.EqualToAvatar,
    children: structure.children,
  }
}

/** The range of an ABI integer type (`uintN` / `intN`). */
const intRange = (type: ParamType): { min: bigint; max: bigint } => {
  const bits = Number(type.type.replace(/^u?int/, "") || "256")
  return type.type.startsWith("uint")
    ? { min: 0n, max: (1n << BigInt(bits)) - 1n }
    : { min: -(1n << BigInt(bits - 1)), max: (1n << BigInt(bits - 1)) - 1n }
}

const intType = (abiType: ParamType, name: string): ParamType => {
  const type = ParamType.from(abiType)
  if (!type.type.startsWith("uint") && !type.type.startsWith("int")) {
    throw new Error(`\`${name}\` is only supported for uint and int params`)
  }
  return type
}

const inRange = (
  type: ParamType,
  name: string,
  value: BigNumberish
): bigint => {
  const v = BigInt(value)
  const { min, max } = intRange(type)
  if (v < min || v > max) {
    throw new Error(
      `\`${name}(${v})\` is out of range for ${type.type} (${min} to ${max})`
    )
  }
  return v
}

const passStatic = () => ({
  paramType: Encoding.Static,
  operator: Operator.Pass,
})

/**
 * Asserts that the value from calldata is greater than the given value
 * @param value The reference value to encode
 */
export const gt =
  (value: BigNumberish): ConditionFunction<BigNumberish> =>
  (abiType: ParamType) => {
    const type = intType(abiType, "gt")
    const v = inRange(type, "gt", value)
    if (v === intRange(type).max) {
      throw new Error(
        `\`gt(${v})\` never passes: it is the maximum of ${type.type}`
      )
    }
    return {
      paramType: Encoding.Static,
      operator: type.type.startsWith("uint")
        ? Operator.GreaterThan
        : Operator.SignedIntGreaterThan,
      compValue: abiEncode([type], [v]),
    }
  }

/**
 * Asserts that the value from calldata is greater than or equal to the given value
 * @param value The reference value to encode
 */
export const gte =
  (value: BigNumberish): ConditionFunction<BigNumberish> =>
  (abiType: ParamType) => {
    const type = intType(abiType, "gte")
    const v = inRange(type, "gte", value)
    // every value is at least the minimum
    if (v === intRange(type).min) return passStatic()
    return gt(v - 1n)(type)
  }

/**
 * Asserts that the value from calldata is less than the given value
 * @param value The reference value to encode
 */
export const lt =
  (value: BigNumberish): ConditionFunction<BigNumberish> =>
  (abiType: ParamType) => {
    const type = intType(abiType, "lt")
    const v = inRange(type, "lt", value)
    if (v === intRange(type).min) {
      throw new Error(
        `\`lt(${v})\` never passes: it is the minimum of ${type.type}`
      )
    }
    return {
      paramType: Encoding.Static,
      operator: type.type.startsWith("uint")
        ? Operator.LessThan
        : Operator.SignedIntLessThan,
      compValue: abiEncode([type], [v]),
    }
  }

/**
 * Asserts that the value from calldata is less than or equal to the given value
 * @param value The reference value to encode
 */
export const lte =
  (value: BigNumberish): ConditionFunction<BigNumberish> =>
  (abiType: ParamType) => {
    const type = intType(abiType, "lte")
    const v = inRange(type, "lte", value)
    // every value is at most the maximum
    if (v === intRange(type).max) return passStatic()
    return lt(v + 1n)(type)
  }

/**
 * Asserts that the bits selected by the mask, at the given byte offset, equal
 * the given value.
 *
 * The mask and value cover `N` bytes, the longer of the two (the shorter is
 * zero-padded on the right). The value must have `N` bytes from the offset,
 * or the check fails: at most 32 for a static parameter, the byte length for
 * `bytes` and `string`.
 */
export const bitmask =
  ({ shift = 0, mask, value }: Bitmask): ConditionFunction<BytesLike> =>
  (abiType: ParamType) => {
    const paramType = parameterType(ParamType.from(abiType))

    if (paramType !== Encoding.Static && paramType !== Encoding.Dynamic) {
      throw new Error(
        `Bitmask can only be used for parameters with type Static or Dynamic, got: ${Encoding[paramType]}`
      )
    }

    if (!Number.isInteger(shift) || shift < 0 || shift >= 65536) {
      throw new Error("shift is out of range, must be between 0 and 65535")
    }

    const maskBytes = getBytes(mask)
    const valueBytes = getBytes(value)
    const n = Math.max(maskBytes.length, valueBytes.length)
    if (n === 0) {
      throw new Error("mask must not be empty")
    }
    // compValue: 2 bytes shift, n bytes mask, n bytes value, at most 65535
    if (2 + 2 * n > 65535) {
      throw new Error("mask is too long, maximum length is 32766 bytes")
    }
    if (paramType === Encoding.Static && shift + n > 32) {
      throw new Error(
        `bitmask never passes: shift + length (${shift + n}) exceeds the 32 bytes of a static value`
      )
    }

    const m = zeroPadRight(maskBytes, n)
    const v = zeroPadRight(valueBytes, n)
    if (v.some((byte, i) => (byte & ~m[i]) !== 0)) {
      throw new Error(
        "bitmask never passes: value has bits set that the mask does not select"
      )
    }

    return {
      paramType,
      operator: Operator.Bitmask,
      compValue: hexlify(concat([toBeHex(shift, 2), m, v])) as `0x${string}`,
    }
  }

interface Bitmask {
  /** Offset in bytes at which to apply the mask, defaults to `0` */
  shift?: number
  /** Each `1` bit selects the bit at that position for the comparison */
  mask: BytesLike
  /** The expected value of the selected bits */
  value: BytesLike
}

function zeroPadRight(value: Uint8Array, length: number): Uint8Array {
  const result = new Uint8Array(length)
  result.set(value, 0)
  return result
}
