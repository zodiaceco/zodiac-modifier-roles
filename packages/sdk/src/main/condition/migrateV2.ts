import { Condition, Encoding, Operator } from "../types"
import { canReorderAnd } from "./normalize/effects"

/**
 * A condition as Roles v2 stores and emits it (`ConditionFlat` events, the
 * subgraph's `condition.json`).
 */
export interface ConditionV2 {
  paramType: number
  operator: number
  compValue?: string
  children?: readonly ConditionV2[]
}

/** v2 `ParameterType` (`Types.sol`). */
const V2 = {
  None: 0,
  Static: 1,
  Dynamic: 2,
  Tuple: 3,
  Array: 4,
  Calldata: 5,
  AbiEncoded: 6,
} as const

/** v2 operators v3 has under the same code. */
const SAME_OP = new Set([
  0, 1, 2, 5, 6, 7, 15, 16, 17, 18, 19, 20, 21, 22, 28, 30,
])
const V2_NOR = 3
const V2_ARRAY_SUBSET = 8
const V2_ETHER_WITHIN_ALLOWANCE = 29

export class MigrateV2Error extends Error {
  constructor(
    message: string,
    /** Child indices from the root to the node. */
    readonly path: readonly number[]
  ) {
    super(`${message} (at ${path.length ? path.join(".") : "root"})`)
  }
}

/**
 * Converts a Roles v2 condition into the v3 condition that enforces the same
 * thing. The differences:
 *
 * - **Encodings.** v2 `Calldata` (4 leading bytes, not compared) and
 *   `AbiEncoded` (none) are both v3 `AbiEncoded`, with the leading-byte
 *   count in its compValue (empty means 4).
 * - **Ether allowance.** v2 `EtherWithinAllowance` is v3 `WithinAllowance` on
 *   `EtherValue`.
 * - **Checks that read no parameter** (`CallWithinAllowance`, ether
 *   allowances) may sit among a `Matches`'s children in v2. v3 Integrity
 *   requires every child of a `Matches` to read a parameter, so they move
 *   next to it: `And[Matches[...], CallWithinAllowance]`. All of them must
 *   pass either way, and charges add up the same in any order, unless a
 *   choice depends on what was charged before (an `Or` with a charging
 *   branch, `canReorderAnd`). Then v2's order is kept, with the checks before
 *   or after the `Matches`; when they sit between its parameters, the
 *   migration throws.
 * - **`Pass` on `None`** is a v2 no-op child; it is dropped.
 * - **Below a `Pass`**, v2 evaluates nothing: the children only describe the
 *   type. They become plain `Pass` type descriptions (v3 requires
 *   descriptions without `And`/`Or`/`Matches`), and a root `Pass` becomes
 *   `Pass` on `None` (no restriction).
 *
 * Throws `MigrateV2Error` for what v3 cannot express: `Nor` and
 * `ArraySubset` (v3 reuses code 8 for `ArrayTailMatches`), and an `EqualTo`
 * on a non-inlined value with a compValue of one word or less. v2 drops that
 * word and compares against the hash of what is left, so such a condition
 * never passes.
 */
export const migrateConditionV2 = (condition: ConditionV2): Condition =>
  convert(condition, [], true)

const isLogical = (c: ConditionV2) =>
  c.operator === Operator.And || c.operator === Operator.Or

/** v2 `Topology.isStructural`: the node reads a parameter. */
const isStructural = (c: ConditionV2): boolean =>
  isLogical(c) ? (c.children ?? []).some(isStructural) : c.paramType !== V2.None

/** v2 `Topology.isInline` for the offset rule of `EqualTo`. */
const isInline = (c: ConditionV2): boolean => {
  switch (c.paramType) {
    case V2.Static:
      return true
    case V2.Tuple:
      return (c.children ?? []).every(isInline)
    case V2.None:
      return (c.children ?? []).every(isInline)
    default:
      return false
  }
}

const isNoOp = (c: ConditionV2) =>
  c.operator === Operator.Pass && c.paramType === V2.None

const PASS_NONE: Condition = {
  paramType: Encoding.None,
  operator: Operator.Pass,
}

const compValueOf = (c: ConditionV2): `0x${string}` | undefined =>
  c.compValue && c.compValue !== "0x"
    ? (c.compValue.toLowerCase() as `0x${string}`)
    : undefined

const convert = (
  c: ConditionV2,
  path: number[],
  isRoot: boolean
): Condition => {
  const { operator: op, paramType: pt } = c
  if (op === V2_NOR) throw new MigrateV2Error("Nor has no v3 equivalent", path)
  if (op === V2_ARRAY_SUBSET)
    throw new MigrateV2Error("ArraySubset has no v3 equivalent", path)
  if (op !== V2_ETHER_WITHIN_ALLOWANCE && !SAME_OP.has(op))
    throw new MigrateV2Error(`unknown v2 operator ${op}`, path)
  if (pt < V2.None || pt > V2.AbiEncoded)
    throw new MigrateV2Error(`unknown v2 paramType ${pt}`, path)

  if (op === V2_ETHER_WITHIN_ALLOWANCE) {
    const compValue = compValueOf(c)
    return {
      paramType: Encoding.EtherValue,
      operator: Operator.WithinAllowance,
      ...(compValue ? { compValue } : {}),
    }
  }

  if (
    op === Operator.EqualTo &&
    !isInline(c) &&
    ((c.compValue ?? "0x").length - 2) / 2 <= 32
  ) {
    throw new MigrateV2Error(
      "EqualTo on a non-inlined value with a compValue of at most one word never passes in v2",
      path
    )
  }

  const children = c.children ?? []
  const calldata = pt === V2.Calldata || pt === V2.AbiEncoded
  const node = (kids: Condition[]): Condition => {
    const compValue =
      pt === V2.AbiEncoded && op === Operator.Matches
        ? ("0x0000" as const)
        : compValueOf(c)
    return {
      paramType: calldata ? Encoding.AbiEncoded : (pt as Encoding),
      operator: op as Operator,
      ...(compValue ? { compValue } : {}),
      ...(kids.length ? { children: kids } : {}),
    }
  }
  const sub = (x: ConditionV2, i: number) => convert(x, [...path, i], false)

  if (op === Operator.Or) {
    if (children.some(isNoOp))
      throw new MigrateV2Error("Or with a Pass on None always passes", path)
    return node(children.map(sub))
  }

  if (op === Operator.And) {
    const kids = children
      .map((x, i) => [x, i] as const)
      .filter(([x]) => !isNoOp(x))
      .map(([x, i]) => sub(x, i))
    return kids.length ? node(kids) : PASS_NONE
  }

  if (op === Operator.Pass) {
    // v2 never evaluates a Pass's children: they only describe the type
    if (isRoot) return PASS_NONE
    return typeDesc(c) ?? PASS_NONE
  }

  if (op === Operator.Matches) {
    const reads = children
      .map((x, i) => [x, i] as const)
      .filter(([x]) => isStructural(x))
    const restAt = children
      .map((x, i) => [x, i] as const)
      .filter(([x]) => !isStructural(x) && !isNoOp(x))
    const rest = restAt.map(([x, i]) => sub(x, i))
    if (reads.length === 0) {
      if (isRoot) {
        if (rest.length === 0) return PASS_NONE
        return rest.length === 1
          ? rest[0]
          : { paramType: Encoding.None, operator: Operator.And, children: rest }
      }
      if (calldata && rest.length === 0) {
        // nested calldata nothing is read from: the plain bytes
        return { paramType: Encoding.Dynamic, operator: Operator.Pass }
      }
      throw new MigrateV2Error(
        "Matches without a child that reads a parameter",
        path
      )
    }
    const readKids = reads.map(([x, i]) => sub(x, i))
    const matches = node(readKids)
    if (!rest.length) return matches
    // v2 evaluates the children in order; moving the checks is safe only if
    // no choice depends on what was charged before
    let kids = [matches, ...rest]
    if (!canReorderAnd([...readKids, ...rest])) {
      const firstRead = reads[0][1]
      const lastRead = reads[reads.length - 1][1]
      if (restAt.every(([, i]) => i < firstRead)) kids = [...rest, matches]
      else if (!restAt.every(([, i]) => i > lastRead))
        throw new MigrateV2Error(
          "allowance checks between parameters whose checks choose which allowance to charge",
          path
        )
    }
    return { paramType: Encoding.None, operator: Operator.And, children: kids }
  }

  return node(children.map(sub))
}

/**
 * The v3 `Pass` description of the value a v2 node reads, or `undefined`
 * for a node that reads none. Nested calldata is a `bytes` value.
 */
const typeDesc = (c: ConditionV2): Condition | undefined => {
  if (isLogical(c)) {
    const first = (c.children ?? []).find(isStructural)
    return first && typeDesc(first)
  }
  const kids = (c.children ?? []).filter(isStructural).map((x) => typeDesc(x)!)
  switch (c.paramType) {
    case V2.Static:
      return { paramType: Encoding.Static, operator: Operator.Pass }
    case V2.Dynamic:
    case V2.Calldata:
    case V2.AbiEncoded:
      return { paramType: Encoding.Dynamic, operator: Operator.Pass }
    case V2.Tuple:
      return {
        paramType: Encoding.Tuple,
        operator: Operator.Pass,
        children: kids,
      }
    case V2.Array:
      return {
        paramType: Encoding.Array,
        operator: Operator.Pass,
        children: kids.slice(0, 1),
      }
    default:
      return undefined
  }
}
