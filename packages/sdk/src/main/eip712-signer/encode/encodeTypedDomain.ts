import { TypedData, TypedDataDomain } from "abitype"

import { domainFields } from "../types/index"
import { encodeTypedMessage } from "./encodeTypedMessage"

export function encodeTypedDomain({
  domain,
  types,
}: {
  domain: TypedDataDomain
  /** Typed data; its `EIP712Domain`, if declared, sets the domain fields. */
  types?: TypedData
}): `0x${string}` {
  return encodeTypedMessage({
    types: { EIP712Domain: domainFields(domain, types) },
    message: domain,
  })
}
