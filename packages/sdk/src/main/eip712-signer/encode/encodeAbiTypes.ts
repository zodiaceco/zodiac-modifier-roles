import { TypedData, TypedDataDomain } from "abitype"
import { AbiCoder } from "ethers"

import { toAbiTypes } from "./toAbiTypes"

export function encodeAbiTypes({
  domain,
  types,
  primaryType,
}: {
  domain?: TypedDataDomain
  types: TypedData
  primaryType?: string
}) {
  const nodes = toAbiTypes({ domain, types, primaryType })
  return AbiCoder.defaultAbiCoder().encode(
    ["tuple(uint256,uint8,bytes32)[]"],
    [nodes.map((n) => [n.parent, n.encoding, n.typeHash])]
  ) as `0x${string}`
}
