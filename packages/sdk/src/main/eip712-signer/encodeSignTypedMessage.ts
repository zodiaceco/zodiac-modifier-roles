import { TypedData, TypedDataDomain } from "abitype"
import { BytesLike, Interface, keccak256, toUtf8Bytes } from "ethers"

import {
  encodeAbiTypes,
  encodeTypedDomain,
  encodeTypedMessage,
  toAbiTypes,
} from "./encode"
import { findPrimaryType, selectTypes } from "./types"
import { MessageStructOf, PrimaryType } from "./typedDataTypes"

const iface = Interface.from([
  "function signMessage(bytes message)",
  "function personalSign(bytes message)",
  "function signTypedMessage(bytes domain, bytes message, (uint256 parent, uint8 encoding, bytes32 typeHash)[] types)",
])

export function encodeSignTypedMessage<
  const T extends TypedData,
  P extends keyof T & string = PrimaryType<T> & string,
>({
  domain,
  types,
  primaryType: declaredPrimaryType,
  message,
}: {
  domain: TypedDataDomain
  types: T
  primaryType?: P extends "EIP712Domain" ? never : P
  message: MessageStructOf<T, P> extends Record<string, any>
    ? MessageStructOf<T, P>
    : never
}) {
  const primaryType = declaredPrimaryType ?? findPrimaryType({ types })
  const selected = selectTypes({ types, primaryType })

  /*
   * We want to hit the correct roles rule, and so we hash the types, and use
   * 4 leading bytes to determine the selector entrypoint within SignTypedMessageLib
   */
  const selector = keccak256(
    encodeAbiTypes({ domain, types: selected, primaryType })
  ).slice(0, 10)

  const data = iface.encodeFunctionData("signTypedMessage", [
    encodeTypedDomain({ domain, types: selected }),
    encodeTypedMessage({ types: selected, primaryType, message }),
    toAbiTypes({ domain, types: selected, primaryType }).map((n) => [
      n.parent,
      n.encoding,
      n.typeHash,
    ]),
  ])

  return `${selector}${data.slice(10)}` as `0x${string}`
}

/**
 * Encodes `signMessage(bytes)`, Safe's `SignMessageLib` scheme. On Safe
 * 1.5.0+ the approval is only verifiable through `isValidSignature(bytes32)`,
 * so `message` must be a 32-byte hash there.
 */
export function encodeSignMessage({ message }: { message: BytesLike }) {
  return iface.encodeFunctionData("signMessage", [message]) as `0x${string}`
}

/**
 * Encodes `personalSign(bytes)`. Like viem's `signMessage`, a string is
 * signed as its UTF-8 text, and `{ raw }` as the given bytes (the hex
 * payload of a `personal_sign` request).
 */
export function encodePersonalSign({
  message,
}: {
  message: string | { raw: BytesLike }
}) {
  return iface.encodeFunctionData("personalSign", [
    typeof message === "string" ? toUtf8Bytes(message) : message.raw,
  ]) as `0x${string}`
}
