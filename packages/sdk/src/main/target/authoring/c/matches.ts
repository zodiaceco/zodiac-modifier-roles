import { BigNumberish, isHexString, ParamType } from "ethers"
import { Condition, Operator, Encoding } from "../../../types"

import { coercePermission } from "../../../permission/coercePermission"
import { scopedType } from "../../../condition/conditionIntegrity"
import { describeStructure } from "./helpers/describeStructure"
import { isFixedArray, parameterType } from "./helpers/parameterType"

import { and } from "./branching"
import { bitmask, eq } from "./comparison"

import { FunctionPermission } from "../../../permission"
import { encodeKey } from "../../../keys"
import {
  ConditionFunction,
  Scoping,
  StructScoping,
  TupleScopings,
} from "../types"

type AbiTypeInput = string | ParamType

/**
 * Matches a tuple or array against a structure of conditions.
 *
 * Throws if the type is not a tuple or array. Throws if the structure of conditions is incompatible with the type.
 * @param scoping The conditions on the tuple or array elements
 */
export const matches =
  <S extends TupleScopings<any> | StructScoping<any>>(scoping: S) =>
  (abiType: ParamType) => {
    // The type system allows for nesting matches(matches()).
    // While using this in practice would not make too much sense, we must make sure it's valid nonetheless.
    if (typeof scoping === "function") {
      return scoping(abiType)
    }

    let conditions: (Condition | undefined)[]

    if (abiType.baseType === "tuple" && !abiType.components) {
      throw new Error("Tuple type must have components")
    }
    if (abiType.baseType === "array" && !abiType.arrayChildren) {
      throw new Error("Array type must have arrayChildren")
    }

    if (Array.isArray(scoping)) {
      // scoping is an array (TupleScopings)

      // supported for tuple and array types
      if (abiType.baseType !== "tuple" && abiType.baseType !== "array") {
        throw new Error(
          `Can only use \`matches\` on tuple or array type params, got: ${abiType.type}`
        )
      }

      // map scoping items to conditions
      conditions = scoping.map((scoping, index) =>
        mapScoping(
          scoping,
          abiType.baseType === "tuple"
            ? abiType.components![index]
            : abiType.arrayChildren!
        )
      )
    } else {
      // scoping is an object (StructScoping)

      // only supported for tuple types
      if (abiType.baseType !== "tuple") {
        throw new Error(
          `Can only use \`matches\` with scoping object on tuple type params, got: ${abiType.type}`
        )
      }

      // map scoping values to conditions
      conditions = abiType.components!.map((componentType) =>
        mapScoping(scoping[componentType.name], componentType)
      )
    }

    // sanity checks
    assertValidConditionsLength(conditions, abiType)
    assertValidConditionsKeys(scoping, abiType)
    assertCompatibleParamTypes(conditions, abiType)

    // A fixed-size array is a tuple: every element needs a child, also the
    // ones the scoping leaves out.
    if (isFixedArray(abiType)) {
      conditions = Array.from(
        { length: abiType.arrayLength! },
        (_, i) => conditions[i]
      )
    }

    return {
      paramType: parameterType(abiType),
      operator: Operator.Matches,
      children: conditions.map(
        (condition, index) =>
          condition ||
          describeStructure(
            abiType.baseType === "tuple"
              ? abiType.components![index]
              : abiType.arrayChildren!
          )
      ),
    }
  }

const calldataMatchesScopings =
  <S extends TupleScopings<any>>(
    scopings: S,
    abiTypes: readonly AbiTypeInput[],
    options: {
      selector?: `0x${string}`
      callWithinAllowance?: string
    } = {}
  ) =>
  (abiType?: ParamType) => {
    const paramTypes = abiTypes.map((abiType) => ParamType.from(abiType))

    // only supported at the top level or for bytes type params
    if (abiType && abiType.type !== "bytes") {
      throw new Error(
        `Can only use \`calldataMatches\` on bytes type params, got: ${abiType.type}`
      )
    }

    const { selector, callWithinAllowance } = options

    // map scoping items to conditions
    const conditions: (Condition | undefined)[] = paramTypes.map(
      (type, index) => mapScoping(scopings[index], type)
    )

    // sanity checks
    assertValidConditionsKeys(conditions, paramTypes)
    assertCompatibleParamTypes(conditions, paramTypes)

    const matchesCondition = {
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: conditions.map(
        (condition, index) => condition || describeStructure(paramTypes[index])
      ),
    }

    if (callWithinAllowance) {
      matchesCondition.children.push({
        paramType: Encoding.None,
        operator: Operator.CallWithinAllowance,
        compValue: encodeKey(callWithinAllowance),
      })
    }

    if (selector) {
      if (selector.length !== 10) {
        throw new Error(
          `Selector must be exactly 4 bytes long, got: ${selector.length}`
        )
      }

      return and(
        () => matchesCondition,
        bitmask({ mask: "0xffffffff", value: selector })
      )(ParamType.from("bytes"))
    }

    return matchesCondition
  }

const calldataMatchesFunctionPermission =
  (functionPermission: FunctionPermission) => (abiType?: ParamType) => {
    // only supported at the top level or for bytes type params
    if (abiType && abiType.type !== "bytes") {
      throw new Error(
        `Can only use \`calldataMatches\` on bytes type params, got: ${abiType.type}`
      )
    }

    const { selector, condition } = coercePermission(functionPermission)
    if (condition) {
      if (
        condition.operator !== Operator.Matches ||
        condition.paramType !== Encoding.AbiEncoded
      ) {
        throw new Error(
          `calldataMatches expects a function permission with an \`Operator.matches\`, \`ParamType.AbiEncoded\` condition, got: \`Operator.${
            Operator[condition.operator]
          }\`, \`ParamType.${Encoding[condition.paramType]}\``
        )
      }
    }

    const selectorCondition = bitmask({
      mask: "0xffffffff0000000000000000000000",
      value: selector,
    })

    return (
      condition ? and(() => condition, selectorCondition) : selectorCondition
    )(ParamType.from("bytes"))
  }

type CalldataMatches = {
  /**
   * Matches the parameters part of EVM call data against a structure of conditions.
   *
   * Skips over the first 4 bytes (function selector) and matches the ABI encoded parameters against the structure of conditions.
   * Optionally, also checks the function selector.
   *
   * @param scoping The conditions structure over the decoded parameters
   * @param abiTypes The parameter types defining how to decode bytes
   * @param selector If set, checks that the 4 bytes function selector matches the given value
   **/
  <S extends TupleScopings<any>>(
    scopings: S,
    abiTypes: readonly AbiTypeInput[],
    options?: {
      selector?: `0x${string}`
      callWithinAllowance?: string
    }
  ): (abiType?: ParamType) => Condition

  /**
   * Matches EVM call data against a reference function permission.
   *
   * The 4 bytes function selector is checked against the function permission selector.
   * Also, function permission condition is evaluated on the call data.
   *
   * @param functionPermission The reference function permission
   **/
  (functionPermission: FunctionPermission): (abiType?: ParamType) => Condition
}

export const calldataMatches: CalldataMatches = <S extends TupleScopings<any>>(
  scopingsOrFunctionPermission: S | FunctionPermission,
  abiTypes?: readonly AbiTypeInput[],
  options?: {
    selector?: `0x${string}`
    callWithinAllowance?: string
  }
): ((abiType?: ParamType) => Condition) => {
  return abiTypes
    ? calldataMatchesScopings(
        scopingsOrFunctionPermission as S,
        abiTypes,
        options
      )
    : calldataMatchesFunctionPermission(
        scopingsOrFunctionPermission as unknown as FunctionPermission
      )
}

/**
 * Matches standard ABI encoded bytes against a structure of conditions.
 *
 * @param scoping The conditions structure over the decoded parameters
 * @param abiTypes The parameter types defining how to decode bytes
 **/
export const abiEncodedMatches =
  <S extends TupleScopings<any>>(scopings: S, abiTypes: AbiTypeInput[]) =>
  (abiType?: ParamType) => {
    const paramTypes = abiTypes.map((abiType) => ParamType.from(abiType))

    // only supported at the top level or for bytes type params
    if (abiType && abiType.type !== "bytes") {
      throw new Error(
        `Can only use \`abiEncodedMatches\` on bytes type params, got: ${abiType.type}`
      )
    }

    // map scoping items to conditions
    const conditions: (Condition | undefined)[] = paramTypes.map(
      (type, index) => mapScoping(scopings[index], type)
    )

    // sanity checks
    assertValidConditionsKeys(conditions, paramTypes)
    assertCompatibleParamTypes(conditions, paramTypes)

    return {
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: conditions.map(
        (condition, index) => condition || describeStructure(paramTypes[index])
      ),
    }
  }

/**
 * Maps a scoping (shortcut notation or condition function) to a condition.
 * @param scoping The scoping to map.
 * @param abiType The abi type of the parameter the scoping applies to.
 * @returns
 */
export function mapScoping(
  scoping: Scoping<any> | undefined,
  abiType: ParamType
): Condition | undefined {
  if (scoping === undefined) {
    return undefined
  }

  let conditionFunction: ConditionFunction<any>

  if (typeof scoping === "function") {
    // scoping is already a condition function
    conditionFunction = scoping
  } else if (
    typeof scoping === "boolean" ||
    typeof scoping === "string" ||
    typeof scoping === "number" ||
    Array.isArray(scoping) ||
    isBigNumberish(scoping)
  ) {
    // placeholders, primitive values, and arrays default to eq condition
    conditionFunction = eq(scoping)
  } else {
    // object values default to matches condition
    conditionFunction = matches(scoping)
  }

  return conditionFunction(abiType)
}

const assertValidConditionsLength = (
  conditions: (Condition | undefined)[],
  typeOrTypes: ParamType | ParamType[]
) => {
  let expectedLength: number
  if (Array.isArray(typeOrTypes)) {
    expectedLength = typeOrTypes.length
  } else if (typeOrTypes.baseType === "tuple" && typeOrTypes.components) {
    expectedLength = typeOrTypes.components.length
  } else if (typeOrTypes.baseType === "array") {
    expectedLength = typeOrTypes.arrayLength || -1
  } else {
    throw new Error(
      `Can only use \`matches\` on tuple or array type params, got: \`${typeOrTypes.format(
        "sighash"
      )}\``
    )
  }

  if (expectedLength <= 0) return

  if (conditions.length > expectedLength) {
    throw new Error(
      `The conditions structure has too many elements (expected length: ${expectedLength}, conditions length: ${conditions.length})`
    )
  }
}

const assertValidConditionsKeys = (
  structure: TupleScopings<any> | StructScoping<any>,
  typeOrTypes: ParamType | ParamType[]
) => {
  if (Array.isArray(structure)) return
  if (!Array.isArray(typeOrTypes) && typeOrTypes.baseType !== "tuple") return

  const types = Array.isArray(typeOrTypes)
    ? typeOrTypes
    : typeOrTypes.components!

  const unusedStructureKeys = arrayDiff(
    Object.keys(structure),
    types.map((type) => type.name)
  )

  if (unusedStructureKeys.length > 0) {
    throw new Error(
      `The conditions structure has unknown keys: ${unusedStructureKeys.join(
        ", "
      )}`
    )
  }
}

const assertCompatibleParamTypes = (
  conditions: (Condition | undefined)[],
  typeOrTypes: ParamType | ParamType[]
) => {
  conditions.forEach((condition, index) => {
    if (!condition) return
    let type: ParamType

    if (Array.isArray(typeOrTypes)) {
      type = typeOrTypes[index]
    } else if (typeOrTypes.baseType === "tuple" && typeOrTypes.components) {
      type = typeOrTypes.components[index]
    } else if (typeOrTypes.baseType === "array" && typeOrTypes.arrayChildren) {
      type = typeOrTypes.arrayChildren
    } else {
      throw new Error(
        `Can only use \`matches\` on tuple or array type params, got: \`${typeOrTypes.format(
          "sighash"
        )}\``
      )
    }

    const expectedType = parameterType(type)
    const scoped = scopedType(condition)

    if (scoped === expectedType) return

    // allow dynamic type values to be interpreted as abi encoded
    if (expectedType === Encoding.Dynamic && scoped === Encoding.AbiEncoded) {
      return
    }

    const fieldReference = type.name ? `'${type.name}'` : `at index ${index}`
    throw new Error(
      `Condition for field ${fieldReference} has wrong paramType \`${Encoding[scoped]}\` (expected: \`${Encoding[expectedType]}\`)`
    )
  })
}

const arrayDiff = (a: string[], b: string[]) => {
  const set = new Set(b)
  return a.filter((x) => !set.has(x))
}

function isBigNumberish(value: any): value is BigNumberish {
  return (
    (typeof value === "number" && value % 1 === 0) ||
    typeof value === "bigint" ||
    (typeof value === "string" && !!value.match(/^-?[0-9]+$/)) ||
    isHexString(value)
  )
}
