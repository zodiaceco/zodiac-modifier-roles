import { TypedData } from "abitype"
import { AbiCoder } from "ethers"

import { findPrimaryType, parseType } from "../types/index"

export function encodeTypedMessage({
  types,
  message,
}: {
  types: TypedData
  message: Record<string, any>
}): `0x${string}` {
  const primaryType = findPrimaryType({ types })

  const fields = types[primaryType]
  return AbiCoder.defaultAbiCoder().encode(
    fields.map((field) => abiType(types, field.type)),
    fields.map((field) => abiValue(types, message[field.name], field.type))
  ) as `0x${string}`
}

function abiType(types: TypedData, type: string): string {
  const { type: baseType, isStruct, isArray, fixedLength } = parseType(type)

  if (isStruct) {
    return `tuple(${types[type]
      .map((field) => abiType(types, field.type))
      .join(",")})`
  } else if (isArray && fixedLength) {
    return `tuple(${new Array(fixedLength)
      .fill(abiType(types, baseType))
      .join(",")})`
  } else if (isArray && !fixedLength) {
    return `${abiType(types, baseType)}[]`
  } else {
    return type
  }
}

function abiValue(types: TypedData, value: any, type: string): any {
  const { type: baseType, isStruct, isArray } = parseType(type)

  if (isStruct) {
    return types[type].map((field) =>
      abiValue(types, value[field.name], field.type)
    )
  } else if (isArray) {
    return value.map((child: unknown) => abiValue(types, child, baseType))
  } else {
    return value
  }
}
