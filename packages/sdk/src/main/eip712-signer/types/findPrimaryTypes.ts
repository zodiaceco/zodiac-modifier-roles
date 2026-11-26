import { TypedData } from "abitype"

import { baseType } from "./parseType"

export function findPrimaryType({ types }: { types: TypedData }): string {
  const rootTypes = findRootTypes({ types })

  const candidates = rootTypes.filter((type) => type !== "EIP712Domain")

  if (candidates.length !== 1) {
    throw new Error(
      candidates.length === 0
        ? "Cannot find the primary type: every message struct is referenced by another"
        : `Cannot infer the primary type, candidates: ${candidates.join(", ")}. Pass primaryType`
    )
  }

  return candidates[0]
}

export function findRootTypes({ types }: { types: TypedData }): string[] {
  const count: Record<string, number> = {}

  Object.keys(types).forEach((typeName) => {
    count[typeName] = 0
  })

  for (const name of Object.keys(types)) {
    for (const field of types[name]!) {
      const type = baseType(field.type)
      if (count[type] !== undefined) {
        count[type]++
      }
    }
  }

  const result = Object.entries(count)
    .filter(([_, count]) => count == 0)
    .map(([type]) => type)

  return [
    result.includes("EIP712Domain") ? "EIP712Domain" : null,
    ...result.filter((type) => type != "EIP712Domain"),
  ].filter(Boolean) as string[]
}
