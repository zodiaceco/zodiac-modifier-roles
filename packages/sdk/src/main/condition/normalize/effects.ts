import { Condition, Operator } from "../../types"

/**
 * Effects a condition subtree can have on the evaluation of its siblings.
 *
 * The Roles evaluator threads two kinds of state through And/Or:
 * - allowance consumptions: copy-on-write, so a failing Or branch leaves no
 *   trace, but every passing child adds its charge;
 * - plucked values: written into shared context and never rolled back, and
 *   read by later Zip, WithinRatio and Custom nodes.
 *
 * Normalization may only reorder or drop children when these effects allow it.
 */

const CHARGING = new Set([
  Operator.WithinAllowance,
  Operator.CallWithinAllowance,
  Operator.Custom, // a custom adapter can return allowance consumptions
])

const has = (c: Condition, pred: (op: Operator) => boolean): boolean =>
  pred(c.operator) || (c.children ?? []).some((child) => has(child, pred))

/** The subtree may charge an allowance when it passes. */
export const charges = (c: Condition) => has(c, (op) => CHARGING.has(op))

/** The subtree writes Pluck slots that siblings may read. */
export const writesSlots = (c: Condition) =>
  has(c, (op) => op === Operator.Pluck)

/**
 * And children may be reordered unless one writes Pluck slots (a later
 * sibling may read them). Charges add up the same in any order.
 */
export const canReorderAnd = (children: readonly Condition[]) =>
  !children.some(writesSlots)

/**
 * Or children may be reordered unless one charges or writes slots: the first
 * passing branch decides which allowance is charged and which values are
 * plucked.
 */
export const canReorderOr = (children: readonly Condition[]) =>
  !children.some((c) => writesSlots(c) || charges(c))
