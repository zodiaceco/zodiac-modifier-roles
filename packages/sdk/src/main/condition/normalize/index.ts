import { Encoding, Condition, Operator } from "../../types"

import { conditionId, rawConditionId } from "../conditionId"
import { padToMatchTypeTree } from "./padToMatchTypeTree"
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
 */
export function normalizeCondition(condition: Condition): Condition {
  let result: Condition = {
    ...condition,
    children: condition.children?.map((child) => normalizeCondition(child)),
  }

  result = cleanEmptyFields(result) // Remove undefined fields
  result = prunePassNodes(result) // Trim trailing Pass nodes
  result = padToMatchTypeTree(result) // Ensure TypeTree compatibility

  result = flattenNestedBranches(result) // Collapse nested AND/OR
  result = dedupeChildren(result) // Remove duplicate branches
  result = unwrapSingleChild(result) // Remove single-child Logical nodes

  result = pushDownOr(result, normalizeCondition)
  result = sortBranchesCanonical(result) // Establish canonical ordering

  return result
}

/** Removes trailing Pass nodes from Matches on AbiEncoded and dynamic tuples (as long as the tuple stays marked dynamic) */
const prunePassNodes = (condition: Condition): Condition => {
  if (!condition.children) return condition
  if (condition.operator !== Operator.Matches) return condition

  const isDynamicTuple =
    condition.paramType === Encoding.Tuple && isDynamicParamType(condition)

  // We must not apply this to static tuples since removing Static Pass nodes would cause word shifts in the encoding.
  const canPrune = condition.paramType === Encoding.AbiEncoded || isDynamicTuple

  if (!canPrune) return condition

  const isGlobalAllowance = (child: Condition) =>
    child.operator === Operator.CallWithinAllowance

  // keep all children nodes with Encoding.None
  // (CallWithinAllowance conditions appear as children of AbiEncoded.Matches)
  const tailChildren = condition.children.filter(isGlobalAllowance)
  const prunableChildren = condition.children.filter(
    (child) => !isGlobalAllowance(child)
  )

  // Start from the end and prune all trailing Pass nodes.
  // Always keep the first child, even if it is a Pass, because children must not be empty.
  // For tuples keep all children up to the first dynamic child.
  let keepChildrenUntil = 0
  if (isDynamicTuple) {
    keepChildrenUntil = prunableChildren.findIndex(isDynamicParamType)
  }
  let prunedChildren: Condition[] = prunableChildren.slice(
    0,
    keepChildrenUntil + 1
  )
  for (let i = prunableChildren.length - 1; i > keepChildrenUntil; i--) {
    const child = prunableChildren[i]
    if (child.operator !== Operator.Pass) {
      prunedChildren = prunableChildren.slice(0, i + 1)
      break
    }
  }

  condition.children = [...prunedChildren, ...tailChildren]
  return condition
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
      const id = rawConditionId(child)
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

    const sorted = condition.children
      .map((c) => ({
        condition: c,
        id: BigInt(conditionId(c)),
        raw: rawConditionId(c),
      }))
      // conditionId is not injective: break ties with the raw id
      .sort((a, b) =>
        a.id !== b.id
          ? a.id < b.id
            ? -1
            : 1
          : a.raw < b.raw
            ? -1
            : a.raw > b.raw
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

const isDynamicParamType = (condition: Condition): boolean => {
  switch (condition.paramType) {
    case Encoding.Static:
      return false
    case Encoding.Dynamic:
    case Encoding.Array:
      return true
    case Encoding.Tuple:
    case Encoding.AbiEncoded:
    case Encoding.None:
      return condition.children?.some(isDynamicParamType) ?? false
    default:
      throw new Error(`Unknown paramType: ${condition.paramType}`)
  }
}
