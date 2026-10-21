import { Condition, Operator, Encoding } from "../types"

export const checkRootConditionIntegrity = (condition: Condition): void => {
  const rootType = checkConsistentChildrenTypes(condition)
  if (rootType !== Encoding.AbiEncoded) {
    throw new Error(
      `Root param type must be \`AbiEncoded\`, got \`${Encoding[rootType]}\``
    )
  }
  checkConditionIntegrityRecursive(condition)
}

export const checkConditionIntegrity = (condition: Condition): void => {
  checkConsistentChildrenTypes(condition)
  checkConditionIntegrityRecursive(condition)
}

/**
 * Validates that logical condition children have consistent types.
 * Since the children conditions address the very same value it does not make sense for them to declare incompatible param types.
 * */
const checkConsistentChildrenTypes = (condition: Condition): Encoding => {
  // EtherValue checks and Zips read no parameter of their own
  if (condition.paramType === Encoding.EtherValue) return Encoding.None
  if (
    condition.operator === Operator.ZipSome ||
    condition.operator === Operator.ZipEvery
  ) {
    return Encoding.None
  }
  if (condition.paramType !== Encoding.None) {
    return condition.paramType
  }

  const childTypes = (condition.children || []).map(
    checkConsistentChildrenTypes
  )
  const expectedType =
    childTypes.find((t) => t !== Encoding.None) ?? Encoding.None

  childTypes.forEach((childType) => {
    checkParameterTypeCompatibility(expectedType, childType)
  })

  return expectedType
}

export const checkParameterTypeCompatibility = (
  left: Encoding,
  right: Encoding
): void => {
  if (right === Encoding.None) return

  if (right === left) return

  if (right === Encoding.Dynamic && left === Encoding.AbiEncoded) {
    return
  }

  if (right === Encoding.AbiEncoded && left === Encoding.Dynamic) {
    throw new Error(
      `Mixed children types: \`${Encoding[right]}\` must appear before \`${Encoding[left]}\``
    )
  }

  throw new Error(
    `Inconsistent children types (\`${Encoding[left]}\` and \`${Encoding[right]}\`)`
  )
}

const checkConditionIntegrityRecursive = (condition: Condition): void => {
  condition.children?.forEach(checkConditionIntegrityRecursive)

  checkParamTypeIntegrity(condition)
  checkCompValueIntegrity(condition)
  checkChildrenIntegrity(condition)
}

const checkParamTypeIntegrity = (condition: Condition): void => {
  const COMPATIBLE_TYPES: Record<Operator, Encoding[]> = {
    [Operator.Pass]: [
      Encoding.Static,
      Encoding.Dynamic,
      Encoding.Tuple,
      Encoding.Array,
      Encoding.AbiEncoded,
      Encoding.EtherValue,
    ],

    [Operator.And]: [Encoding.None],
    [Operator.Or]: [Encoding.None],

    [Operator.Empty]: [Encoding.None],

    [Operator.Matches]: [Encoding.AbiEncoded, Encoding.Tuple, Encoding.Array],

    [Operator.ArraySome]: [Encoding.Array],
    [Operator.ArrayEvery]: [Encoding.Array],
    [Operator.ArrayTailMatches]: [Encoding.Array],

    [Operator.ZipSome]: [Encoding.None],
    [Operator.ZipEvery]: [Encoding.None],

    [Operator.Slice]: [Encoding.Static, Encoding.Dynamic],
    [Operator.Pluck]: [Encoding.Static, Encoding.EtherValue, Encoding.Array],

    [Operator.EqualToAvatar]: [Encoding.Static],
    [Operator.EqualTo]: [
      Encoding.Static,
      Encoding.Dynamic,
      Encoding.Tuple,
      Encoding.Array,
      Encoding.EtherValue,
    ],

    [Operator.GreaterThan]: [Encoding.Static, Encoding.EtherValue],
    [Operator.LessThan]: [Encoding.Static, Encoding.EtherValue],
    [Operator.SignedIntGreaterThan]: [Encoding.Static, Encoding.EtherValue],
    [Operator.SignedIntLessThan]: [Encoding.Static, Encoding.EtherValue],

    [Operator.Bitmask]: [Encoding.Static, Encoding.Dynamic],

    [Operator.Custom]: [
      Encoding.Static,
      Encoding.Dynamic,
      Encoding.Tuple,
      Encoding.Array,
      Encoding.EtherValue,
    ],

    [Operator.WithinRatio]: [Encoding.None],

    [Operator.WithinAllowance]: [Encoding.Static, Encoding.EtherValue],

    [Operator.CallWithinAllowance]: [Encoding.None],
  }
  const compatibleTypes = COMPATIBLE_TYPES[condition.operator]

  if (!compatibleTypes.includes(condition.paramType)) {
    throw new Error(
      `\`${
        Operator[condition.operator]
      }\` condition not supported for paramType \`${
        Encoding[condition.paramType]
      }\``
    )
  }
}

const checkCompValueIntegrity = (condition: Condition): void => {
  const requiresCompValue =
    condition.operator >= Operator.EqualTo ||
    condition.operator === Operator.Slice ||
    condition.operator === Operator.Pluck ||
    condition.operator === Operator.ZipSome ||
    condition.operator === Operator.ZipEvery

  // AbiEncoded Matches may carry leading bytes (2-byte count + prefix)
  if (
    condition.operator === Operator.Matches &&
    condition.paramType === Encoding.AbiEncoded
  ) {
    return
  }

  if (requiresCompValue && !condition.compValue) {
    throw new Error(
      `\`${Operator[condition.operator]}\` condition must have a compValue`
    )
  }

  if (!requiresCompValue && condition.compValue) {
    throw new Error(
      `\`${Operator[condition.operator]}\` condition cannot have a compValue`
    )
  }
}

const checkChildrenIntegrity = (condition: Condition): void => {
  if (
    condition.paramType === Encoding.Tuple ||
    condition.paramType === Encoding.Array
  ) {
    if (!condition.children || condition.children.length === 0) {
      throw new Error(
        `Condition on \`${
          Encoding[condition.paramType]
        }\` params must have children to describe the type structure, found violation in \`${
          Operator[condition.operator]
        }\` condition`
      )
    }
  }

  if (condition.operator === Operator.ArrayEvery) {
    if (condition.children?.length !== 1) {
      throw new Error(
        `\`${
          Operator[condition.operator]
        }\` conditions must have exactly one child`
      )
    }
  }

  if (
    condition.operator === Operator.Matches ||
    condition.operator === Operator.ArrayTailMatches
  ) {
    if (!condition.children || condition.children.length === 0) {
      throw new Error(
        `\`${Operator[condition.operator]}\` conditions must have children`
      )
    }
  }

  if (
    condition.operator >= Operator.EqualToAvatar &&
    condition.operator !== Operator.Custom && // TODO Does this make sense? Can Custom have children?
    condition.paramType !== Encoding.AbiEncoded &&
    condition.paramType !== Encoding.Tuple &&
    condition.paramType !== Encoding.Array
  ) {
    if (condition.children && condition.children?.length > 0) {
      throw new Error(
        `\`${Operator[condition.operator]}\` condition on \`${
          Encoding[condition.paramType]
        }\` type param must not have children`
      )
    }
  }

  if (
    condition.operator === Operator.And ||
    condition.operator === Operator.Or
  ) {
    if (!condition.children || condition.children.length === 0) {
      throw new Error(
        `\`${Operator[condition.operator]}\` condition must have children`
      )
    }
  }
}
