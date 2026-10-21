import { Condition, Encoding, Operator } from "../../types"

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

/** The subtree has a choice node (Or, ArraySome, ZipSome) over branches that charge. */
export const choosesCharge = (c: Condition): boolean =>
  ((c.operator === Operator.Or ||
    c.operator === Operator.ArraySome ||
    c.operator === Operator.ZipSome) &&
    charges(c)) ||
  (c.children ?? []).some(choosesCharge)

/**
 * And children may be reordered unless one writes Pluck slots (a later
 * sibling may read them). Charges add up the same in any order, as long as
 * no choice depends on what was charged before: a child that picks among
 * charging branches (Or[W1, W2]) must be the only child that charges.
 */
export const canReorderAnd = (children: readonly Condition[]) =>
  !children.some(writesSlots) &&
  (children.filter(charges).length <= 1 || !children.some(choosesCharge))

/**
 * Or children may be reordered unless one charges or writes slots: the first
 * passing branch decides which allowance is charged and which values are
 * plucked.
 */
export const canReorderOr = (children: readonly Condition[]) =>
  !children.some((c) => writesSlots(c) || charges(c))

/**
 * The node reads a parameter: Matches children that are not structural do
 * not consume a parameter position. Same rule as the contract's TypeTree:
 * And/Or are structural if any child is, other nodes unless their encoding
 * is None or EtherValue.
 */
export const isStructural = (c: Condition): boolean =>
  c.operator === Operator.And || c.operator === Operator.Or
    ? (c.children ?? []).some(isStructural)
    : c.paramType !== Encoding.None && c.paramType !== Encoding.EtherValue
