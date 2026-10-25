import { TypedDataDomain, TypedDataParameter } from "abitype"

/**
 * The `EIP712Domain` fields to use: the declared ones when `types` has
 * `EIP712Domain` (the dapp's own definition, which its verifying contract
 * hashes), else the fields present in `domain`, in EIP-712 order.
 */
export function domainFields(
  domain: TypedDataDomain | undefined,
  types?: Record<string, readonly TypedDataParameter[]>
): TypedDataParameter[] {
  if (types?.EIP712Domain) return [...types.EIP712Domain]
  return typesForDomain(domain ?? {})
}

export function typesForDomain(domain: TypedDataDomain): TypedDataParameter[] {
  return [
    typeof domain?.name === "string" && { name: "name", type: "string" },
    domain?.version && { name: "version", type: "string" },
    (typeof domain?.chainId === "number" ||
      typeof domain?.chainId === "bigint") && {
      name: "chainId",
      type: "uint256",
    },
    domain?.verifyingContract && {
      name: "verifyingContract",
      type: "address",
    },
    domain?.salt && { name: "salt", type: "bytes32" },
  ].filter(Boolean) as TypedDataParameter[]
}
