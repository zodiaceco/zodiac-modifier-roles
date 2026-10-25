import { Encoding, Condition, Operator } from "../../types"

import { conditionId } from "../conditionId"
import { pushDownOr } from "./pushDownOr"
import { canReorderAnd, canReorderOr, charges, writesSlots } from "./effects"

/**
 * Normalizes a condition by transforming its structure without altering its semantics.
 * The goal is to minimize tree size and produce a canonical (normal) form, so that
 * semantically equivalent conditions are structurally identical.
 *
 * This normalization enables efficient condition equality checks and supports globally
 * deduplicated storage. In particular, the Roles contract stores conditions as bytecode
 * at addresses derived from hashing the condition data — so structurally consistent
 * representations help avoid redundant storage.
 *
 * That the rewrites keep the meaning is proven in Lean, against a
 * transcription of this code (packages/evm/formal/Normalize); effects.ts
 * holds the rules for reordering and removing children.
 *
 * Children of a `Matches` are never removed, trailing `Pass` nodes included:
 * the contract computes every child's location before evaluating any, so
 * dropping one would change which calldata it accepts.
 */
export function normalizeCondition(condition: Condition): Condition {
  // A Pluck's array and a Zip's fields must keep their types exactly (the
  // contract checks that each Zip field matches the plucked element type),
  // so their subtrees are left as written.
  if (
    condition.operator === Operator.Pluck ||
    condition.operator === Operator.ZipSome ||
    condition.operator === Operator.ZipEvery
  ) {
    return condition
  }

  let result: Condition = {
    ...condition,
    children: condition.children?.map((child) => normalizeCondition(child)),
  }

  result = cleanEmptyFields(result) // Remove undefined fields

  result = flattenNestedBranches(result) // Collapse nested AND/OR
  result = dedupeChildren(result) // Remove duplicate branches
  result = unwrapSingleChild(result) // Remove single-child Logical nodes

  result = pushDownOr(result, normalizeCondition)
  result = sortBranchesCanonical(result) // Establish canonical ordering

  return result
}

/** flatten nested AND/OR conditions */
const flattenNestedBranches = (condition: Condition): Condition => {
  if (
    condition.operator === Operator.And ||
    condition.operator === Operator.Or
  ) {
    if (!condition.children) return condition

    const flattenedChildren = condition.children.flatMap((child) =>
      child.operator === condition.operator ? child.children || [] : [child]
    )
    condition.children = flattenedChildren
  }

  return condition
}

/**
 * remove duplicate child branches in AND/OR
 * (an AND keeps duplicates that charge an allowance: each copy charges again;
 * nothing is removed next to children that write Pluck slots, since a later
 * copy may read slots a sibling wrote in between)
 */
const dedupeChildren = (condition: Condition): Condition => {
  if (
    condition.operator === Operator.And ||
    condition.operator === Operator.Or
  ) {
    if (condition.children?.some(writesSlots)) return condition
    const isAnd = condition.operator === Operator.And
    const seen = new Set<string>()
    const uniqueChildren = condition.children?.filter((child) => {
      const id = conditionId(child)
      if (seen.has(id)) return isAnd && charges(child)

      seen.add(id)
      return true
    })

    condition.children = uniqueChildren
  }

  return condition
}

/** remove AND/OR wrapping if they have only a single child */
const unwrapSingleChild = (condition: Condition): Condition => {
  if (
    condition.operator === Operator.And ||
    condition.operator === Operator.Or
  ) {
    return condition.children?.length === 1 ? condition.children[0] : condition
  }

  return condition
}

/**
 * enforce a canonical order of AND/OR branches
 * (unless reordering would change which allowance is charged or which
 * Pluck slots are written before they are read, see ./effects)
 */
const sortBranchesCanonical = (condition: Condition): Condition => {
  if (
    condition.operator === Operator.And ||
    condition.operator === Operator.Or
  ) {
    if (!condition.children) return condition

    const canReorder =
      condition.operator === Operator.And
        ? canReorderAnd(condition.children)
        : canReorderOr(condition.children)
    if (!canReorder) return condition
    // a Zip must stay after the child that describes the value (the
    // logical node's size is its first child's that fits)
    if (
      condition.children.some(
        (c) =>
          c.operator === Operator.ZipSome || c.operator === Operator.ZipEvery
      )
    )
      return condition

    const sorted = condition.children
      .map((c) => ({
        condition: c,
        id: conditionId(c),
      }))
      // shorter ids first, then by content
      .sort((a, b) =>
        a.id.length !== b.id.length
          ? a.id.length - b.id.length
          : a.id < b.id
            ? -1
            : a.id > b.id
              ? 1
              : 0
      )
      .map(({ condition }) => condition)

    // in case of mixed-type children (dynamic & abiEncoded), those with children must come first
    const front = sorted.filter(
      (child) => child.paramType === Encoding.AbiEncoded
    )
    const back = sorted.filter(
      (child) => child.paramType !== Encoding.AbiEncoded
    )
    return {
      ...condition,
      children: [...front, ...back],
    }
  }

  return condition
}

const cleanEmptyFields = (condition: Condition): Condition => {
  if ("children" in condition && !condition.children) delete condition.children
  if ("compValue" in condition && !condition.compValue)
    delete condition.compValue
  return condition
}
