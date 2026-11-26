import { TypedData } from "abitype"
import { AbiCoder, keccak256, ParamType } from "ethers"
import { Condition, Encoding, Operator } from "../types"
import { SIGN_TYPED_MESSAGE_LIB_ADDRESS } from "../addresses"

import { c } from "../target/authoring"
import { StructScoping } from "../target/authoring/types"
import { encodeAbiTypes, toAbiTypes } from "./encode"
import { findPrimaryType, parseType, selectTypes } from "./types"
import { DomainStructOf, MessageStructOf, PrimaryType } from "./typedDataTypes"

/**
 * Returns a permission allowing the role to sign EIP-712 typed messages
 * matching the given domain and message conditions.
 *
 * The returned permission targets `SignTypedMessageLib` under a selector
 * deterministically derived from `types`, so different EIP-712 layouts can be
 * scoped under the same target without colliding.
 *
 * @param params
 * @param params.types - EIP-712 type definitions, including `EIP712Domain` and
 *   the primary message struct. Should be declared `as const` so TypeScript
 *   can narrow field types and infer the primary type.
 * @param params.primaryType - The primary message struct, as the signing
 *   request names it. May be omitted when it is the one struct no other
 *   struct references. Types it does not reach are dropped.
 * @param params.domain - Struct scoping over the `EIP712Domain` fields. Field
 *   names, primitive types, and nested struct shapes are inferred from
 *   `params.types`. Omitted fields are unconstrained; the whole struct may
 *   also be a {@link ConditionFunction} (e.g. `c.pass`).
 * @param params.message - Struct scoping over the primary message struct. Same
 *   inference rules as `domain`.
 * @returns A permission targeting `SignTypedMessageLib` with the right
 *   selector, delegatecall flag, and condition tree wired up.
 */
export function allowSignTypedMessage<
  const T extends TypedData,
  P extends keyof T & string = PrimaryType<T> & string,
>({
  types: declared,
  primaryType: declaredPrimaryType,
  domain,
  message,
}: {
  types: T
  primaryType?: P extends "EIP712Domain" ? never : P
  domain: DomainStructOf<T> extends Record<string, any>
    ? StructScoping<DomainStructOf<T>>
    : never
  message: MessageStructOf<T, P> extends Record<string, any>
    ? StructScoping<MessageStructOf<T, P>>
    : never
}): {
  targetAddress: `0x${string}`
  selector: `0x${string}`
  delegatecall: true
  condition: Condition
} {
  if (!declared["EIP712Domain"]) {
    throw new Error("TypedData does not include EIP712Domain")
  }

  const primaryType: string =
    declaredPrimaryType ?? findPrimaryType({ types: declared })
  const types = selectTypes({ types: declared, primaryType })

  const selector = keccak256(encodeAbiTypes({ types, primaryType })).slice(
    0,
    10
  ) as `0x${string}`

  return {
    targetAddress: SIGN_TYPED_MESSAGE_LIB_ADDRESS,
    selector,
    delegatecall: true,
    condition: {
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        toAbiEncodedCondition(types, "EIP712Domain", domain),
        toAbiEncodedCondition(types, primaryType, message),
        typesCondition(types, primaryType),
      ],
    },
  }
}

/**
 * Converts a struct scoping over an EIP-712 named struct into a Condition
 * with `paramType: AbiEncoded`, by delegating to `c.matches` against a
 * named-tuple ABI type derived from the EIP-712 type tree.
 */
function toAbiEncodedCondition(
  types: TypedData,
  typeName: string,
  scoping: unknown
): Condition {
  const tupleAbiType = ParamType.from(buildTupleAbiType(types, typeName))
  const tupleCondition = c.matches(scoping as any)(tupleAbiType)

  return {
    paramType: Encoding.AbiEncoded,
    operator: Operator.Matches,
    // Inner AbiEncoded matches a `bytes` parameter directly (no function
    // selector prefix), so set leadingBytes = 0. Without this, the on-chain
    // packer defaults leadingBytes to 4 and the condition fails to match.
    compValue: "0x0000",
    children: tupleCondition.children,
  }
}

/** Builds a named-tuple ABI type string for an EIP-712 struct. */
function buildTupleAbiType(types: TypedData, typeName: string): string {
  const fields = types[typeName]
  return `tuple(${fields
    .map(
      (f: { name: string; type: string }) =>
        `${buildAbiType(types, f.type)} ${f.name}`
    )
    .join(",")})`
}

/** Recursively builds an ABI type string for an EIP-712 field type. */
function buildAbiType(types: TypedData, typeStr: string): string {
  const { type, isStruct, isArray, fixedLength } = parseType(typeStr)
  if (isStruct) {
    return buildTupleAbiType(types, type)
  }
  if (isArray && fixedLength) {
    return `${buildAbiType(types, type)}[${fixedLength}]`
  }
  if (isArray) {
    return `${buildAbiType(types, type)}[]`
  }
  return typeStr
}

function typesCondition(types: TypedData, primaryType: string): Condition {
  const nodes = toAbiTypes({ types, primaryType })
  const compValue = AbiCoder.defaultAbiCoder().encode(
    ["tuple(uint256,uint8,bytes32)[]"],
    [nodes.map((n) => [n.parent, n.encoding, n.typeHash])]
  )

  return {
    paramType: Encoding.Array,
    operator: Operator.EqualTo,
    compValue: compValue as any,
    children: [
      {
        paramType: Encoding.Tuple,
        operator: Operator.Pass,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.Pass,
          },
          {
            paramType: Encoding.Static,
            operator: Operator.Pass,
          },
          {
            paramType: Encoding.Static,
            operator: Operator.Pass,
          },
        ],
      },
    ],
  }
}
