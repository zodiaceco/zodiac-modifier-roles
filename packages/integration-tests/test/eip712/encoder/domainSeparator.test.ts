import assert from "node:assert/strict"
import { after, describe, it } from "node:test"
import { network } from "hardhat"
import { getTypesForEIP712Domain, hashDomain, keccak256, toBytes } from "viem"

import { __integration } from "zodiac-roles-sdk"

const { encodeTypedDomain, toAbiTypes } = __integration

const connection = await network.create()
const { viem, networkHelpers } = connection
const { loadFixture } = networkHelpers

async function deployEIP712Encoder() {
  const encoder = await viem.deployContract("MockEIP712Encoder")

  return { encoder }
}

describe("EIP712Encoder", () => {
  after(async () => {
    await connection.close()
  })

  describe("hashDomainSeparator()", () => {
    it("should hash the domain separator with all required fields", async () => {
      const { encoder } = await loadFixture(deployEIP712Encoder)

      const domain = {
        name: "Ether Mail",
        version: "abc",
        chainId: 9,
        verifyingContract:
          "0xCcCCccccCCCCcCCCCCCcCcCccCcCCCcCcccccccC" as `0x${string}`,
        salt: keccak256(toBytes("Hello World")),
      }

      assert.equal(
        await encoder.read.hashTypedDomain([
          encodeTypedDomain({ domain }),
          toAbiTypes({ domain }).map((n) => ({
            parent: BigInt(n.parent),
            encoding: n.encoding,
            typeHash: n.typeHash,
          })),
        ]),
        hashDomain<Record<string, unknown>>({
          domain,
          types: { EIP712Domain: getTypesForEIP712Domain({ domain }) },
        })
      )
    })

    it("should handle custom salt usage in the domain separator", async () => {
      const { encoder } = await loadFixture(deployEIP712Encoder)

      const domain = {
        chainId: 35377,
        verifyingContract:
          "0x00000000000000000000000000000000000fffff" as `0x${string}`,
        salt: keccak256(toBytes("Here is a custom salt")),
      }

      assert.equal(
        await encoder.read.hashTypedDomain([
          encodeTypedDomain({ domain }),
          toAbiTypes({ domain }).map((n) => ({
            parent: BigInt(n.parent),
            encoding: n.encoding,
            typeHash: n.typeHash,
          })),
        ]),
        hashDomain<Record<string, unknown>>({
          domain,
          types: { EIP712Domain: getTypesForEIP712Domain({ domain }) },
        })
      )
    })
  })
})
