import { Condition, Operator } from "../../types"
import {
  createTypeTree,
  isArray,
  isComplex,
  isLogical,
  TypeTree,
  typeTreeId,
} from "../typeTree"
import { isStructural } from "./effects"

export function padToMatchTypeTree(condition: Condition): Condition {
  /*
   * This function is to be used from within normalizeCondition we operate
   * under the assumption that lower levels were recursively normalized thus we
   * only really wanna kick off the normalization for Logical or Array nodes
   */
  if (!isLogical(condition) && !isArray(condition)) {
    return condition
  }

  const isPaddeable = (c: Condition) => isLogical(c) || isComplex(c)

  // type trees are only defined for nodes with populated children
  if (!(condition.children || []).filter(isPaddeable).every(hasTypeTree)) {
    return condition
  }

  const typeTreeIds = new Set(
    (condition.children || [])
      .filter(isPaddeable)
      .map((child) => typeTreeId(child))
  )

  // All paddeable children already match
  if (typeTreeIds.size <= 1) {
    return condition
  }

  /*
   *
   * Apply all nodes onto eachother, cumulatively
   *
   * Since type trees can vary in structure at different depths, no single tree
   * is always "longest" everywhere. Tree A might have more nodes in one subtree
   * while Tree B has more in another. Padding each child with the structure
   * from all others, we ensure uniform structure across all branches, because
   * padding is cumulative
   */
  const nextChildren = [...condition.children!]
  for (let i = 0; i < condition.children!.length; i++) {
    if (!isPaddeable(nextChildren[i])) continue

    for (let j = 0; j < nextChildren.length; j++) {
      if (j == i || !isPaddeable(nextChildren[j])) continue

      nextChildren[i] = extendWithPassNodes(
        nextChildren[i],
        createTypeTree(nextChildren[j])!
      )
    }
  }

  return {
    ...condition,
    children: nextChildren,
  }
}

/*
 * Pads a `condition` with Pass nodes, such that it structurally matches a typeTree
 *
 * Assumptions:
 * - `condition` and `typeTree` are structurally compatible (not checked here).
 * - Either may be a subset of the other.
 * - If `condition` is missing branches that exist in `typeTree`, they are added.
 * - If `condition` is wider (has extra nodes), they are preserved — nothing is removed.
 *
 */
function extendWithPassNodes(
  condition: Condition | undefined | null,
  typeTree: TypeTree
): Condition {
  if (!condition) {
    condition = {
      operator: Operator.Pass,
      paramType: typeTree.paramType,
    }
  }

  if (isLogical(condition)) {
    return {
      ...condition,
      children: condition.children!.map((child) =>
        extendWithPassNodes(child, typeTree)
      ),
    }
  }

  // only extend a node with a type tree of its own encoding: appending
  // children to, e.g., an array would change what it checks
  if (isComplex(condition) && condition.paramType === typeTree.paramType) {
    const children = (condition.children || []) as Condition[]

    /*
     * Only structural children read a field, and the type tree lists only
     * those: pair them in order, keep the others in place, and append Pass
     * nodes for the fields the condition has no child for.
     */
    let field = 0
    const extended = children.map((child) =>
      isStructural(child) && field < typeTree.children.length
        ? extendWithPassNodes(child, typeTree.children[field++])
        : child
    )
    return {
      ...condition,
      children: [
        ...extended,
        ...typeTree.children
          .slice(field)
          .map((childTypeTree) =>
            extendWithPassNodes(undefined, childTypeTree)
          ),
      ],
    }
  }

  return condition
}

/** createTypeTree succeeds on every node below (and including) `condition` */
function hasTypeTree(condition: Condition): boolean {
  const children = condition.children || []
  if (isLogical(condition) || isComplex(condition)) {
    if (children.length === 0) return false
    if (isArray(condition) && !createTypeTree(children[0])) return false
  }
  return children.every(hasTypeTree)
}
