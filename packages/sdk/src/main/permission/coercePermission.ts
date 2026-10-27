import { ethers, ParamType } from "ethers"

import {
  Permission,
  PermissionCoerced,
  FunctionPermission,
  FunctionPermissionCoerced,
  TargetPermission,
} from "./types"

const sighash = (signature: string) => {
  const fragment = ethers.FunctionFragment.from(signature)
  const selector = ethers.id(fragment.format()).slice(0, 10)
  return selector
}

export const coercePermission = <P extends Permission>(
  permission: P
): P extends FunctionPermission
  ? FunctionPermissionCoerced
  : TargetPermission => {
  if (!/^0x[0-9a-fA-F]{40}$/.test(permission.targetAddress)) {
    throw new Error(`Invalid target address: ${permission.targetAddress}`)
  }

  const selector = () => {
    if ("selector" in permission) {
      if (!/^0x[0-9a-fA-F]{8}$/.test(permission.selector)) {
        throw new Error(
          `Invalid selector (expected 4 bytes hex): ${permission.selector}`
        )
      }
      return { selector: permission.selector.toLowerCase() as `0x${string}` }
    }

    if ("signature" in permission) {
      return { selector: sighash(permission.signature) as `0x${string}` }
    }

    return {}
  }

  const condition = () => {
    if (
      "condition" in permission &&
      typeof permission.condition === "function"
    ) {
      return { condition: permission.condition(ParamType.from("bytes")) }
    }

    if ("condition" in permission) {
      return { condition: permission.condition }
    }

    return {}
  }

  const coerced: PermissionCoerced = {
    targetAddress: permission.targetAddress.toLowerCase() as `0x${string}`,
    ...selector(),
    ...condition(),
    send: Boolean(permission.send),
    delegatecall: Boolean(permission.delegatecall),
  }
  return coerced as any
}
