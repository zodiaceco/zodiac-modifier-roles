import { Condition, Operator } from "../types"
import { conditionId } from "./conditionId"

/**
 * Removes an independently satisfiable path from a condition.
 *
 * This function removes any condition fragment that could independently make the
 * original condition evaluate to true (satisfiable). It works with conditions that
 * have been normalized (where ORs may have been pushed down) or in their original form.
 *
 * Conceptually, if you think of a condition as a set of independent paths that
 * can satisfy it, this function removes one such path:
 * - For `A OR B`, removing A leaves B (removing an explicit path)
 * - For `AND(X, OR(Y, Z))`, removing `AND(X, Y)` leaves `AND(X, Z)`
 *   (removing a path that was pushed down during normalization)
 *
 * The "single hinge" principle:
 * - AND operators use set-based semantics: exactly one child must differ between
 *   condition and fragment, regardless of order. This supports commutative logic
 *   where AND(A, B) ≡ AND(B, A).
 * - MATCHES operators use positional semantics: exactly one position must differ
 *   between condition and fragment. Order matters for structural matching.
 *
 * @param condition The condition to subtract from
 * @param fragment The satisfiable path to remove
 * @returns The remainder after removing the path, or undefined if nothing remains
 * @returns The original condition if the fragment isn't a valid satisfiable path
 *
 * @example
 * - `subtract(OR(A, B, C), B)` → `OR(A, C)`
 * - `subtract(AND(X, OR(Y, Z)), AND(X, Y))` → `AND(X, Z)`
 * - `subtract(AND(A, B, C), AND(C, A, D))` → `AND(A, B, C)` (order-independent)
 */
export function subtractCondition(
  condition: Condition,
  fragment: Condition
): Condition | undefined {
  if (conditionId(condition) === conditionId(fragment)) {
    return undefined
  }

  if (
    condition.operator === Operator.Or &&
    condition.children &&
    fragment.operator === Operator.Or &&
    fragment.children
  ) {
    return or_n_m(condition, fragment)
  }

  if (condition.operator === Operator.Or) {
    return or_n_1(condition, fragment)
  }

  const canProceed =
    (condition.operator == Operator.And ||
      condition.operator == Operator.Matches) &&
    condition.operator === fragment.operator &&
    condition.paramType === fragment.paramType &&
    matchingChildrenCount(condition, fragment)

  if (!canProceed) {
    return condition
  }

  if (condition.operator == Operator.And) {
    return and(condition, fragment)
  } else {
    return matches(condition, fragment)
  }
}

/**
 * Handles OR n:m subtraction.
 * Removes all fragment children from an OR condition if they exist.
 * - If all match: returns the remainder (or unwraps if 1 child remains).
 * - If not all fragment children are found: returns the original condition.
 */
function or_n_m(condition: Condition, fragment: Condition) {
  const conditionChildren = condition.children!
  const fragmentChildren = fragment.children!

  // Ensure all fragment children exist in condition
  const conditionIds = new Set(conditionChildren.map(conditionId))
  const allExist = fragmentChildren.every((child) =>
    conditionIds.has(conditionId(child))
  )
  if (!allExist) return condition

  // Filter out fragment children
  const fragmentIds = new Set(fragmentChildren.map(conditionId))
  const remaining = conditionChildren.filter(
    (child) => !fragmentIds.has(conditionId(child))
  )

  // remove
  if (remaining.length === 0) return undefined
  // unwrap
  if (remaining.length === 1) return remaining[0]
  // filter
  return { ...condition, children: remaining }
}

function or_n_1(condition: Condition, fragment: Condition) {
  const nextChildren = condition
    .children!.map((child) => subtractCondition(child, fragment))
    .filter((t) => !!t)

  // Fragment not in OR
  if (shallowEquals(condition.children!, nextChildren)) return condition

  // remove
  if (nextChildren.length === 0) return undefined
  // unwrap
  if (nextChildren.length === 1) return nextChildren[0]
  // filter
  return { ...condition, children: nextChildren }
}

function and(condition: Condition, fragment: Condition) {
  const children = condition.children!
  const fragmentChildren = fragment.children!
  invariant(children.length == fragmentChildren.length)

  const cIds = children.map(conditionId)
  const fIds = fragmentChildren.map(conditionId)

  const conditionOnlyIds = cIds.filter((id) => !fIds.includes(id))
  const fragmentOnlyIds = fIds.filter((id) => !cIds.includes(id))

  // Single hinge principle: exactly one difference in each direction
  if (conditionOnlyIds.length !== 1 || fragmentOnlyIds.length !== 1) {
    return condition
  }

  const child = children.find(
    (child) => conditionId(child) === conditionOnlyIds[0]
  )!
  const fragmentChild = fragmentChildren.find(
    (child) => conditionId(child) === fragmentOnlyIds[0]
  )!

  const remainder = subtractCondition(child, fragmentChild)
  if (!remainder || remainder === child) {
    // If subtraction failed or didn't change anything, bail
    return condition
  }

  return {
    ...condition,
    children: children.map((c) => (c === child ? remainder : c)),
  }
}

function matches(condition: Condition, fragment: Condition) {
  invariant(condition.operator === Operator.Matches)

  let changes = 0
  const newChildren = condition.children!.map((child, index) => {
    if (changes > 1) return child

    const fragmentChild = fragment.children![index]

    if (conditionId(child) === conditionId(fragmentChild)) {
      return child
    }

    changes++
    const remainder = subtractCondition(child, fragmentChild)
    // If couldn't subtract or would remove entirely, keep original
    if (remainder === child || remainder === undefined) {
      return child
    } else {
      return remainder
    }
  })

  return changes == 1 ? { ...condition, children: newChildren } : condition
}

function shallowEquals<T>(a: readonly T[], b: readonly T[]): boolean {
  return a.length === b.length && a.every((item, index) => item === b[index])
}

function matchingChildrenCount(a: Condition, b: Condition): boolean {
  return (
    Array.isArray(a.children) &&
    Array.isArray(b.children) &&
    a.children.length > 0 &&
    a.children.length == b.children.length
  )
}

function invariant(c: boolean) {
  if (!c) {
    throw new Error("Invariant")
  }
}
