import { Encoding, Condition, Operator } from "../types"
import { isStructural } from "./normalize/effects"

export type TypeTree = {
  paramType: Encoding
  children: TypeTree[]
}

export function typeTreeId(condition: Condition): string {
  return JSON.stringify(createTypeTree(condition))
  // return (
  //   "0x" +
  //   createHash("sha256")
  //     .update(JSON.stringify(createTypeTree(condition)))
  //     .digest("hex")
  // )
}

export function createTypeTree(condition: Condition): TypeTree | null {
  const atLeastOne = (): Condition[] => {
    if (!condition.children || condition.children.length == 0) {
      throw new Error("Expected populated children array")
    }

    return condition.children! as Condition[]
  }

  if (isLogical(condition)) {
    // the type of the first child that reads the parameter, as the
    // contract's TypeTree resolves it (an ether value check reads none)
    const child = atLeastOne().find(isStructural)
    return child ? createTypeTree(child) : null
  }

  if (isArray(condition)) {
    const [child] = atLeastOne()
    return {
      paramType: condition.paramType,
      children: [createTypeTree(child)!],
    }
  }

  if (isComplex(condition)) {
    const children = atLeastOne()

    return {
      paramType: condition.paramType,
      children: children.map(createTypeTree).filter((t) => !!t),
    }
  }

  if (isSimple(condition)) {
    return {
      paramType: condition.paramType,
      children: [],
    }
  }

  return null
}

export function isLogical({ operator }: { operator: Operator }) {
  return [Operator.And, Operator.Or].includes(operator)
}

export function isComplex({ paramType }: { paramType: Encoding }) {
  return [Encoding.AbiEncoded, Encoding.Array, Encoding.Tuple].includes(
    paramType
  )
}

export function isSimple({ paramType }: { paramType: Encoding }) {
  return [Encoding.Dynamic, Encoding.Static].includes(paramType)
}

export function isArray({ paramType }: { paramType: Encoding }) {
  return paramType == Encoding.Array
}
