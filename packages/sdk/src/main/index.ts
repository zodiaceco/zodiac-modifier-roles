export * from "./types"
export { chains } from "./chains"

/*
 *
 * Layer 1 - Target
 *
 */
export { c, forAll } from "./target/authoring"
export { targetIntegrity } from "./target/integrity"

/*
 *
 * Layer 2 - Permission
 *
 */
export type {
  Permission,
  PermissionCoerced,
  TargetPermission,
  FunctionPermission,
  FunctionPermissionCoerced,
  PermissionSet,
  ExecutionFlags,
} from "./permission"

export {
  permissionId,
  coercePermission,
  processPermissions,
  reconstructPermissions,
  targetId,
  validatePresets,
} from "./permission"

/*
 *
 * Condition primitives
 *
 */
export {
  conditionId,
  conditionAddress,
  conditionHash,
} from "./condition/conditionId"
export {
  flattenCondition,
  type ConditionFlat,
} from "./condition/flattenCondition"
export { normalizeCondition } from "./condition/normalize"

/*
 *
 * Misc
 *
 */
export { rolesAbi, posterAbi } from "./abi"
export {
  encodePersonalSign,
  encodeSignMessage,
  encodeSignTypedMessage,
  allowPersonalSign,
  allowSignTypedMessage,
} from "./eip712-signer"
export { encodeKey, decodeKey } from "./keys"
export { postRole } from "./postRole"
export { fetchLicense, License, LicenseError } from "./licensing"

/*
 *
 * Integration? TODO fix
 *
 */
import {
  encodeTypedDomain,
  encodeTypedMessage,
  toAbiTypes,
} from "./eip712-signer/encode"

import { typesForDomain } from "./eip712-signer/types"

export const __integration = {
  encodeTypedDomain,
  encodeTypedMessage,
  toAbiTypes,
  typesForDomain,
}
