import { Condition, Encoding, Operator } from "../../types"
import { siblingsSameType, typeKeyOf } from "../checkStored"

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
 * Or children may be reordered unless one writes slots (a failing branch
 * leaves its writes for the next one). A charging child may move only if it
 * excludes every other child: the first passing branch decides which
 * allowance is charged, and with at most one passing branch, its position
 * does not matter. (`canReorderOr` in the Lean transcription, proven in
 * formal/Normalize/Exclusive.lean.)
 */
export const canReorderOr = (children: readonly Condition[]) => {
  if (children.some(writesSlots)) return false
  const charging = children.map(charges)
  if (!charging.some(Boolean)) return true

  const types = new Map<Condition, string | undefined>()
  const typeOf = (c: Condition) => {
    if (!types.has(c)) types.set(c, typeKeyOf(c))
    return types.get(c)
  }
  const sameType = (a: Condition, b: Condition) => {
    const t = typeOf(a)
    return t !== undefined && t === typeOf(b)
  }
  const excludes = (a: Condition, b: Condition) =>
    sameType(a, b) && disjoint(a, b, sameType)

  for (let i = 0; i < children.length; i++) {
    for (let j = i + 1; j < children.length; j++) {
      const [a, b] = [children[i], children[j]]
      if (charging[i] && !excludes(a, b)) return false
      if (charging[j] && !excludes(b, a)) return false
    }
  }
  return true
}

/**
 * No value passes both conditions, checked against the same parameter:
 * - And: one of its children is disjoint from the other side;
 * - Or: every one of its children is;
 * - Matches on a tuple or calldata, with the same compValue and children of
 *   the same types position by position: two structural children at the
 *   same position are (they read the same field);
 * - static EqualTo on one 32-byte word, with no children: the words differ.
 */
const disjoint = (
  a: Condition,
  b: Condition,
  sameType: (a: Condition, b: Condition) => boolean
): boolean => {
  const recurse = (x: Condition, y: Condition) => disjoint(x, y, sameType)
  const as = a.children ?? []
  const bs = b.children ?? []

  if (a.operator === Operator.And) return as.some((x) => recurse(x, b))
  if (b.operator === Operator.And) return bs.some((y) => recurse(a, y))
  if (a.operator === Operator.Or) return as.every((x) => recurse(x, b))
  if (b.operator === Operator.Or) return bs.every((y) => recurse(a, y))

  if (a.operator === Operator.Matches && b.operator === Operator.Matches) {
    if (a.paramType !== Encoding.Tuple && a.paramType !== Encoding.AbiEncoded) {
      return false
    }
    const sa = as.filter(isStructural)
    const sb = bs.filter(isStructural)
    return (
      a.paramType === b.paramType &&
      hexOf(a.compValue) === hexOf(b.compValue) &&
      as.length === bs.length &&
      as.every((x, i) => sameType(x, bs[i])) &&
      sa.length === sb.length &&
      sa.some((x, i) => recurse(x, sb[i]))
    )
  }

  const x = pinnedWord(a)
  const y = pinnedWord(b)
  return x !== undefined && y !== undefined && x !== y
}

const hexOf = (compValue?: string) => (compValue ?? "0x").toLowerCase()

/** The word a static EqualTo with no children pins. */
const pinnedWord = (c: Condition) =>
  c.operator === Operator.EqualTo &&
  c.paramType === Encoding.Static &&
  (c.children ?? []).length === 0 &&
  /^0x[0-9a-f]{64}$/i.test(c.compValue ?? "")
    ? hexOf(c.compValue)
    : undefined

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

/**
 * The children an `Or` branch merge would put under one node: they must have
 * exactly the same type (the branches the same type tree), so every child
 * reads its value where the branch it came from did.
 */
export const compatibleSiblings = (siblings: readonly Condition[]): boolean =>
  siblingsSameType(siblings)
