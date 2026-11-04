import { Clearance, Function, Target } from "../types"

import { checkAllowanceUnits } from "../allowance"
import { checkRootConditionIntegrity } from "../condition/conditionIntegrity"

export const targetIntegrity = (targets: Target[]): void => {
  const uniqueAddresses = new Set(
    targets.map((target) => target.address.toLowerCase())
  )
  if (uniqueAddresses.size < targets.length) {
    throw new Error("Duplicate target addresses")
  }

  targets.forEach(targetEntry)

  checkAllowanceUnits(
    targets.flatMap((target) =>
      target.functions.flatMap((func) =>
        func.condition ? [func.condition] : []
      )
    )
  )
}

const targetEntry = (target: Target): void => {
  if (
    target.clearance === Clearance.Function &&
    target.functions.length === 0
  ) {
    throw new Error(
      `Function-cleared targets must have at least one function (target in violation: ${target.address})`
    )
  }

  if (target.clearance !== Clearance.Function && target.functions.length > 0) {
    throw new Error(
      `A target with functions must be function-cleared (target in violation: ${target.address})`
    )
  }

  const uniqueFunctionSelectors = new Set(
    target.functions.map((func) => func.selector.toLowerCase())
  )
  if (uniqueFunctionSelectors.size < target.functions.length) {
    throw new Error(`Duplicate functions in target ${target.address}`)
  }

  target.functions.forEach(functionEntry)
}

const functionEntry = (func: Function): void => {
  if (func.wildcarded && func.condition) {
    throw new Error(
      `Wildcarded functions cannot have conditions (function in violation: ${func.selector})`
    )
  }

  if (!func.wildcarded && !func.condition) {
    throw new Error(
      `Non-wildcarded functions must have conditions (function in violation: ${func.selector})`
    )
  }

  if (func.condition) {
    checkRootConditionIntegrity(func.condition)
  }
}
