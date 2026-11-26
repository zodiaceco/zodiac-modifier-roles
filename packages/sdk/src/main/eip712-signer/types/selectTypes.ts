import { TypedData } from "abitype"

import { baseType } from "./parseType"

/**
 * The part of `types` that hashing `primaryType` uses: `EIP712Domain`, if
 * declared, and every struct reachable from `primaryType`. Wallet requests
 * name the primary type and may carry types it does not use, or a struct
 * that references it; without this selection either would be taken for
 * the primary type.
 */
export function selectTypes<T extends TypedData>({
  types,
  primaryType,
}: {
  types: T
  primaryType: string
}): T {
  if (primaryType === "EIP712Domain") {
    throw new Error("primaryType must be the message struct, not EIP712Domain")
  }
  if (!types[primaryType]) {
    throw new Error(`primaryType ${primaryType} is not declared in types`)
  }

  const reachable = new Set<string>()
  const visit = (type: string) => {
    if (type === "EIP712Domain") {
      throw new Error(`${primaryType} must not reference EIP712Domain`)
    }
    if (reachable.has(type) || !types[type]) return
    reachable.add(type)
    for (const field of types[type]) visit(baseType(field.type))
  }
  visit(primaryType)

  const selected: Record<string, TypedData[string]> = {}
  if (types.EIP712Domain) selected.EIP712Domain = types.EIP712Domain
  for (const type of Object.keys(types)) {
    if (reachable.has(type)) selected[type] = types[type]
  }
  return selected as T
}
