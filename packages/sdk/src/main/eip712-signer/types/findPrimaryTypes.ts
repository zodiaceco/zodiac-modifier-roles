import { TypedData } from "abitype"

import { baseType } from "./parseType"

export function findPrimaryType({ types }: { types: TypedData }): string {
  const rootTypes = findRootTypes({ types })

  if (rootTypes.length == 0 || rootTypes.length > 2) {
    throw new Error(`Too many or too few roo types ${rootTypes.join(", ")}`)
  }

  if (rootTypes.length > 1 && rootTypes[0] !== "EIP712Domain") {
    throw new Error(`Roots should start with EIP712Domain`)
  }

  return rootTypes[rootTypes.length - 1]
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
