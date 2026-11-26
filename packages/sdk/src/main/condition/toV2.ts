import { getAddress } from "ethers"

import { AVATAR_IS_OWNER_OF_ERC721_ADDRESS } from "../addresses"
import { Condition, Encoding, Function, Operator, Target } from "../types"
import { ConditionV2 } from "./migrateV2"

/** What a Roles v2 modifier cannot enforce, and where in the condition. */
export interface V2Issue {
  message: string
  /** Child indices from the root to the node. */
  path: readonly number[]
  /** Set by `toTargetsV2`: the target the condition scopes. */
  targetAddress?: `0x${string}`
  /** Set by `toTargetsV2`: the function the condition scopes. */
  selector?: `0x${string}`
}

export class IncompatibleWithV2Error extends Error {
  constructor(readonly issues: readonly V2Issue[]) {
    super(
      [
        "Not supported by Roles v2:",
        ...issues.map((issue) => `- ${describe(issue)}`),
      ].join("\n")
    )
  }
}

const describe = ({ message, path, targetAddress, selector }: V2Issue) =>
  [
    targetAddress && `${targetAddress}${selector ? `.${selector}` : ""}: `,
    message,
    ` (at ${path.length ? path.join(".") : "root"})`,
  ]
    .filter(Boolean)
    .join("")

/** A function as a Roles v2 modifier stores it. */
export interface FunctionV2 extends Omit<Function, "condition"> {
  condition?: ConditionV2
}

/** A target as a Roles v2 modifier stores it. */
export interface TargetV2 extends Omit<Target, "functions"> {
  functions: FunctionV2[]
}

/**
 * The Roles v2 condition that enforces what a v3 condition does, the inverse
 * of `migrateConditionV2`. Throws `IncompatibleWithV2Error` listing every
 * part v2 cannot enforce:
 *
 * - **Operators v2 lacks:** `Empty`, `ArrayTailMatches`, `ZipSome`,
 *   `ZipEvery`, `Slice`, `Pluck` and `WithinRatio`.
 * - **The ether value**, except a `WithinAllowance` on it, which is v2's
 *   `EtherWithinAllowance`.
 * - **Allowance conversions:** a `WithinAllowance` with a price adapter or
 *   with differing decimals. Equal decimals convert nothing and are dropped.
 * - **Leading bytes:** v2 reads calldata after 4 leading bytes (`Calldata`)
 *   or none (`AbiEncoded`), and compares neither. Check a selector with a
 *   `Bitmask` instead.
 * - **Bitmasks** wider than 15 bytes. Narrower ones are padded to v2's fixed
 *   15 bytes. On a static value, trailing bytes the mask does not select are
 *   dropped first. On a dynamic one, v2 only requires the length when the
 *   last byte expects a non-zero value; otherwise the bitmask is refused.
 * - **Custom conditions** without a v2 checker: a checker implements one
 *   version's `ICustomCondition`, so only known v3 checkers map to their v2
 *   counterpart. Extra data must fit v2's 12 bytes.
 * - **`EqualTo` on a non-inlined value** with a compValue of at most one word.
 *   v2 drops that word and compares against the hash of what is left, so it
 *   never passes.
 *
 * The result is not checked against v2's reading rules: run v2's
 * `targetIntegrity` on it before applying.
 */
export const toConditionV2 = (condition: Condition): ConditionV2 => {
  const issues: V2Issue[] = []
  const result = convert(condition, [], issues)
  if (issues.length > 0) throw new IncompatibleWithV2Error(issues)
  return result
}

/** Every part of `condition` a Roles v2 modifier cannot enforce. */
export const v2Issues = (condition: Condition): V2Issue[] => {
  const issues: V2Issue[] = []
  convert(condition, [], issues)
  return issues
}

/**
 * The targets as a Roles v2 modifier stores them. Throws
 * `IncompatibleWithV2Error` listing every issue of every condition, each
 * with its target and function.
 *
 * A function whose condition is `Pass` on `None` (no restriction) becomes
 * wildcarded, as v2 has no condition for that.
 */
export const toTargetsV2 = (targets: readonly Target[]): TargetV2[] => {
  const issues: V2Issue[] = []
  const result = targets.map((target) => ({
    ...target,
    functions: target.functions.map((fn): FunctionV2 => {
      const { condition, ...rest } = fn
      if (condition === undefined) return rest
      if (isPassNone(condition)) return { ...rest, wildcarded: true }
      const found: V2Issue[] = []
      const converted = convert(condition, [], found)
      issues.push(
        ...found.map((issue) => ({
          ...issue,
          targetAddress: target.address,
          selector: fn.selector,
        }))
      )
      return { ...rest, condition: converted }
    }),
  }))
  if (issues.length > 0) throw new IncompatibleWithV2Error(issues)
  return result
}

/** v2 `ParameterType` (`Types.sol`). */
const V2Type = {
  None: 0,
  Static: 1,
  Dynamic: 2,
  Tuple: 3,
  Array: 4,
  Calldata: 5,
  AbiEncoded: 6,
} as const

const V2_ETHER_WITHIN_ALLOWANCE = 29

/** v3 operators v2 has under the same code and with the same compValue. */
const SAME_OP = new Set<Operator>([
  Operator.Pass,
  Operator.And,
  Operator.Or,
  Operator.Matches,
  Operator.ArraySome,
  Operator.ArrayEvery,
  Operator.EqualToAvatar,
  Operator.EqualTo,
  Operator.GreaterThan,
  Operator.LessThan,
  Operator.SignedIntGreaterThan,
  Operator.SignedIntLessThan,
  Operator.CallWithinAllowance,
])

/** v3 encodings v2 has under the same code. */
const SAME_TYPE = new Set<Encoding>([
  Encoding.None,
  Encoding.Static,
  Encoding.Dynamic,
  Encoding.Tuple,
  Encoding.Array,
])

/** Custom condition checkers: v3 address → the v2 checker doing the same. */
const V2_CHECKERS: ReadonlyMap<string, `0x${string}`> = new Map(
  BigInt(AVATAR_IS_OWNER_OF_ERC721_ADDRESS) === 0n
    ? []
    : [
        [
          AVATAR_IS_OWNER_OF_ERC721_ADDRESS.toLowerCase(),
          "0x91b1bd7bcc5e623d5ce76b0152253499a9c819d1",
        ],
      ]
)

const isPassNone = (c: Condition) =>
  c.operator === Operator.Pass &&
  c.paramType === Encoding.None &&
  !c.children?.length

const opName = (op: Operator) => Operator[op] ?? `operator ${op}`

const bytesOf = (hex: string | undefined) =>
  hex && hex !== "0x" ? (hex.length - 2) / 2 : 0

/** v2 `Topology.isInline` for the offset rule of `EqualTo`. */
const isInline = (c: Condition): boolean => {
  switch (c.paramType) {
    case Encoding.Static:
      return true
    case Encoding.Tuple:
    case Encoding.None:
      return (c.children ?? []).every(isInline)
    default:
      return false
  }
}

const convert = (
  c: Condition,
  path: readonly number[],
  issues: V2Issue[]
): ConditionV2 => {
  const issue = (message: string) => {
    issues.push({ message, path })
  }
  const children = (c.children ?? []).map((child, i) =>
    convert(child, [...path, i], issues)
  )
  const node = (
    paramType: number,
    operator: number,
    compValue: string | undefined = c.compValue
  ): ConditionV2 => ({
    paramType,
    operator,
    ...(compValue && compValue !== "0x"
      ? { compValue: compValue.toLowerCase() }
      : {}),
    ...(children.length > 0 ? { children } : {}),
  })

  if (c.paramType === Encoding.EtherValue) {
    if (c.operator !== Operator.WithinAllowance) {
      issue(`${opName(c.operator)} on the ether value is not available`)
      return node(V2Type.None, c.operator)
    }
    return node(V2Type.None, V2_ETHER_WITHIN_ALLOWANCE, allowanceKey(c, issue))
  }

  const paramType = toParamType(c, issue)

  switch (c.operator) {
    case Operator.WithinAllowance:
      return node(paramType, c.operator, allowanceKey(c, issue))
    case Operator.Bitmask:
      return node(
        paramType,
        c.operator,
        toBitmask(c.compValue, c.paramType, issue)
      )
    case Operator.Custom:
      return node(paramType, c.operator, toCustom(c.compValue, issue))
    case Operator.EqualTo:
      if (!isInline(c) && bytesOf(c.compValue) <= 32) {
        issue(
          "EqualTo on a non-inlined value with a compValue of at most one word never passes"
        )
      }
      return node(paramType, c.operator)
    default:
      if (!SAME_OP.has(c.operator)) {
        issue(`${opName(c.operator)} is not available`)
      }
      // v2 compares no leading bytes, so `Matches` on calldata has no compValue
      return node(
        paramType,
        c.operator,
        c.paramType === Encoding.AbiEncoded ? "0x" : c.compValue
      )
  }
}

const toParamType = (c: Condition, issue: (message: string) => void) => {
  if (SAME_TYPE.has(c.paramType)) return c.paramType as number
  if (c.paramType !== Encoding.AbiEncoded) {
    issue(`encoding ${Encoding[c.paramType] ?? c.paramType} is not available`)
    return V2Type.None
  }
  // 2 bytes: the number of leading bytes; then the bytes they must equal
  const cv = c.compValue && c.compValue !== "0x" ? c.compValue : "0x0004"
  const leading = parseInt(cv.slice(2, 6), 16)
  if (bytesOf(cv) > 2) {
    issue(
      "comparing leading bytes is not available, check a selector with a bitmask"
    )
  }
  if (leading === 4) return V2Type.Calldata
  if (leading === 0) return V2Type.AbiEncoded
  issue(`${leading} leading bytes are not available, only 0 or 4`)
  return V2Type.Calldata
}

/**
 * The allowance key of a `WithinAllowance`. A conversion is a key followed by
 * two decimals and an optional price adapter; equal decimals and no adapter
 * convert nothing.
 */
const allowanceKey = (c: Condition, issue: (message: string) => void) => {
  const cv = c.compValue ?? "0x"
  const key = cv.slice(0, 66) as `0x${string}`
  const conversion = cv.slice(66)
  if (conversion === "") return key
  const [balanceDecimals, inputDecimals] = [
    conversion.slice(0, 2),
    conversion.slice(2, 4),
  ]
  if (conversion.length > 4) {
    issue("allowances with a price adapter are not available")
  } else if (balanceDecimals !== inputDecimals) {
    issue("allowances converting between decimals are not available")
  }
  return key
}

/**
 * v3: 2 bytes shift, n bytes mask, n bytes value. It fails unless the value
 * has all `shift + n` bytes, even those the mask does not select.
 * v2: 2 bytes shift, 15 bytes mask, 15 bytes value. It only needs the byte at
 * `shift` and reads zeros past the end, so only a last byte expecting a
 * non-zero value requires the length.
 */
const toBitmask = (
  compValue: string | undefined,
  paramType: Encoding,
  issue: (message: string) => void
) => {
  const cv = (compValue ?? "0x").slice(2)
  const shift = cv.slice(0, 4)
  const n = (cv.length - 4) / 4
  let mask = cv.slice(4, 4 + 2 * n)
  let value = cv.slice(4 + 2 * n)
  if (paramType === Encoding.Static && parseInt(shift, 16) + n > 32) {
    issue("a bitmask reaching past the 32 bytes of a static value never passes")
  }
  // A byte the mask does not select, with no value expected, checks nothing
  // but the length. A static value always has its 32 bytes.
  if (paramType === Encoding.Static) {
    while (mask.endsWith("00") && value.endsWith("00")) {
      mask = mask.slice(0, -2)
      value = value.slice(0, -2)
    }
  } else if (value.endsWith("00")) {
    // v2 reads a missing last byte as zero, and zero is what it expects
    issue(
      "a bitmask on a dynamic value whose last byte expects zero requires a length v2 does not check"
    )
  }
  if (mask.length > 30) {
    issue(`bitmasks are at most 15 bytes, this one is ${mask.length / 2}`)
  }
  return `0x${shift}${mask.padEnd(30, "0")}${value.padEnd(30, "0")}` as const
}

/** v3: checker address, then extra data. v2: address, then 12 bytes extra. */
const toCustom = (
  compValue: string | undefined,
  issue: (message: string) => void
) => {
  const cv = (compValue ?? "0x").toLowerCase()
  const address = cv.slice(0, 42)
  const extra = cv.slice(42)
  const v2Checker = V2_CHECKERS.get(address)
  if (v2Checker === undefined) {
    issue(
      `the custom condition ${addressLabel(address)} has no known v2 checker`
    )
  }
  if (extra.length > 24) {
    issue("custom conditions take at most 12 bytes of extra data")
  }
  return `${v2Checker ?? address}${extra.padEnd(24, "0")}` as const
}

const addressLabel = (address: string) => {
  try {
    return getAddress(address)
  } catch {
    return address
  }
}
