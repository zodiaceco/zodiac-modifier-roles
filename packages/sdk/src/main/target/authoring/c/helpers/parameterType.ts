import { ParamType } from "ethers"
import { Encoding } from "../../../../types"

/** Whether `type` is a fixed-size array `T[k]`. */
export const isFixedArray = (type: ParamType): boolean =>
  type.baseType === "array" &&
  type.arrayLength !== null &&
  type.arrayLength >= 0

/**
 * The encoding of an ABI type. A fixed-size array `T[k]` is encoded like the
 * tuple `(T, ..., T)` (inline when `T` is static, no length word), so it is a
 * `Tuple` with `k` children; only `T[]` is an `Array`.
 */
export const parameterType = (type: ParamType): Encoding => {
  switch (type.baseType) {
    case "tuple":
      return Encoding.Tuple
    case "array":
      return isFixedArray(type) ? Encoding.Tuple : Encoding.Array
    case "string":
    case "bytes":
      return Encoding.Dynamic
    default:
      return Encoding.Static
  }
}
