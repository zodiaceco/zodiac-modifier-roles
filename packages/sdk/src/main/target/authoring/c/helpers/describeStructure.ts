import { ParamType } from "ethers"
import { Condition, Operator } from "../../../../types"

import { isFixedArray, parameterType } from "./parameterType"

/**
 * Given an ABI param type, generates a tree of Pass nodes that matches the structure of the type
 */
export const describeStructure = (type: ParamType): Condition => {
  const children = type.arrayChildren
    ? isFixedArray(type)
      ? Array.from({ length: type.arrayLength! }, () => type.arrayChildren!) // one per element, like a tuple
      : [type.arrayChildren]
    : (type.components as ParamType[] | undefined) // ethers typings are wrong

  return {
    paramType: parameterType(type),
    operator: Operator.Pass,
    children:
      children && children.length > 0
        ? children.map(describeStructure)
        : undefined,
  }
}
