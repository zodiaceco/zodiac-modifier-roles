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

/**
 * The node's encoding has a fixed size and sits in its parent's head (the
 * contract's Topology.isInlined): no Dynamic, Array or AbiEncoded encoding
 * in the subtree. Appending children to an inlined tuple grows it and moves
 * every later parameter.
 */
export const isInlined = (c: Condition): boolean =>
  c.paramType !== Encoding.Dynamic &&
  c.paramType !== Encoding.Array &&
  c.paramType !== Encoding.AbiEncoded &&
  (c.children ?? []).every(isInlined)

/**
 * The type layout the contract derives from a condition (Integrity's
 * `TypeTree.resolve`), as a string: equal strings for equal type hashes.
 * And/Or take the type of their first structural child, unless their
 * structural children differ (a variant: encoding None, all of them); an
 * array takes its first structural child as element type, unless its
 * children differ. Every other node lists its structural children,
 * including the child of a Slice.
 */
type Layout = { encoding: Encoding; children: Layout[] }

const isZero = (l: Layout) =>
  l.encoding === Encoding.None && l.children.length === 0
const layoutKey = (l: Layout): string =>
  l.children.length === 0
    ? `${l.encoding}`
    : `${l.encoding}(${l.children.map(layoutKey).join(",")})`

const isVariant = (layouts: Layout[]): boolean => {
  let prev: Layout | undefined
  for (const l of layouts) {
    if (!prev || isZero(prev)) prev = l
    if (isZero(l)) continue
    if (layoutKey(prev) !== layoutKey(l)) return true
  }
  return false
}

const layout = (c: Condition): Layout => {
  const children = (c.children ?? []).map(layout)
  const variant = isVariant(children)
  if ((c.operator === Operator.And || c.operator === Operator.Or) && !variant) {
    return (
      children.find((l) => !isZero(l)) ?? {
        encoding: Encoding.None,
        children: [],
      }
    )
  }
  const structural = children.filter((l) => !isZero(l))
  return {
    encoding:
      c.paramType === Encoding.EtherValue ? Encoding.None : c.paramType,
    children:
      c.paramType === Encoding.Array && !variant
        ? structural.slice(0, 1)
        : structural,
  }
}

const isDynamicish = (l: Layout) =>
  l.encoding === Encoding.Dynamic ||
  l.encoding === Encoding.AbiEncoded ||
  l.encoding === Encoding.None

/**
 * Integrity accepts these conditions as children of one And/Or
 * (`_validateVariantTypes`): every structural one has the type of the first,
 * or both are bytes-like (Dynamic, AbiEncoded or a variant).
 */
export const compatibleSiblings = (siblings: readonly Condition[]): boolean => {
  let prev: Layout | undefined
  for (const next of siblings.map(layout)) {
    if (!prev || isZero(prev)) prev = next
    if (isZero(next)) continue
    if (
      layoutKey(prev) !== layoutKey(next) &&
      !(isDynamicish(prev) && isDynamicish(next))
    ) {
      return false
    }
  }
  return true
}
