import assert from "node:assert/strict"
import type { TypedData, TypedDataDomain } from "abitype"
import { hashTypedData } from "viem"
import { __integration } from "zodiac-roles-sdk"
import type { NetworkConnection } from "hardhat/types/network"
import "@nomicfoundation/hardhat-viem"
import "@nomicfoundation/hardhat-network-helpers"

const { encodeTypedDomain, encodeTypedMessage, toAbiTypes } = __integration

type Value = Record<string, any>

function findPrimaryType({ types }: { types: TypedData }): string {
  const referenced = new Set<string>()
  for (const fields of Object.values(types)) {
    if (!fields) continue
    for (const field of fields) {
      referenced.add(field.type.split("[")[0])
    }
  }
  const roots = Object.keys(types).filter(
    (name) => name !== "EIP712Domain" && !referenced.has(name)
  )
  if (roots.length !== 1) {
    throw new Error(`Expected exactly 1 primary type, got: ${roots.join(", ")}`)
  }
  return roots[0]
}

export function createCompareToViemHashing({
  viem,
  networkHelpers,
}: Pick<NetworkConnection, "viem" | "networkHelpers">) {
  const { loadFixture } = networkHelpers

  async function deployEIP712Encoder() {
    const encoder = await viem.deployContract("MockEIP712Encoder")

    return { encoder }
  }

  return async function compareToViemHashing({
    domain,
    types,
    message,
  }: {
    domain: TypedDataDomain
    types: TypedData
    message: Value
  }) {
    const { encoder } = await loadFixture(deployEIP712Encoder)

    const _domain = encodeTypedDomain({ domain })
    const _message = encodeTypedMessage({ types, message })
    const abiTypes = toAbiTypes({ domain, types }).map((n) => ({
      parent: BigInt(n.parent),
      encoding: n.encoding,
      typeHash: n.typeHash,
    }))
    const primaryType = findPrimaryType({ types })

    assert.equal(
      await encoder.read.hashTypedMessage([_domain, _message, abiTypes]),
      hashTypedData({ domain, types, primaryType, message })
    )
  }
}
