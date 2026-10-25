import { describe, expect, it } from "vitest"
import { AbiCoder } from "ethers"

import { parseType, typesForDomain, domainFields } from "../types"
import { encodeTypedMessage } from "./encodeTypedMessage"
import { encodeTypedDomain } from "./encodeTypedDomain"
import { toAbiTypes } from "./toAbiTypes"

const abi = AbiCoder.defaultAbiCoder()

describe("parseType", () => {
  it("splits off the outermost array dimension", () => {
    expect(parseType("uint8[2][]")).toMatchObject({
      type: "uint8[2]",
      isArray: true,
      fixedLength: 0,
    })
    expect(parseType("Person[][3]")).toMatchObject({
      type: "Person[]",
      isArray: true,
      fixedLength: 3,
    })
  })

  it("knows every uint<M> / int<M> width", () => {
    for (const t of ["uint24", "uint48", "uint160", "int40", "int248"]) {
      expect(parseType(t).isAtomic).toBe(true)
    }
    expect(parseType("uint7").isAtomic).toBe(false)
  })
})

describe("encodeTypedMessage", () => {
  it("encodes nested arrays dimension by dimension", () => {
    const types = { M: [{ name: "a", type: "uint8[2][]" }] }
    const message = {
      a: [
        [1, 2],
        [3, 4],
      ],
    }
    expect(encodeTypedMessage({ types, message })).toBe(
      abi.encode(["uint8[2][]"], [message.a])
    )
  })

  it("encodes Permit2's PermitDetails (uint160, uint48)", () => {
    const types = {
      PermitDetails: [
        { name: "token", type: "address" },
        { name: "amount", type: "uint160" },
        { name: "expiration", type: "uint48" },
        { name: "nonce", type: "uint48" },
      ],
    }
    const message = {
      token: "0x" + "11".repeat(20),
      amount: 5n,
      expiration: 6n,
      nonce: 7n,
    }
    expect(encodeTypedMessage({ types, message })).toBe(
      abi.encode(
        ["address", "uint160", "uint48", "uint48"],
        [message.token, 5n, 6n, 7n]
      )
    )
  })
})

describe("domain fields", () => {
  it("keeps a bigint chainId", () => {
    expect(typesForDomain({ chainId: 1n })).toEqual([
      { name: "chainId", type: "uint256" },
    ])
  })

  it("uses a declared EIP712Domain, in its order", () => {
    const declared = [
      { name: "chainId", type: "uint256" },
      { name: "name", type: "string" },
    ]
    const domain = { name: "x", chainId: 1 }
    expect(domainFields(domain, { EIP712Domain: declared })).toEqual(declared)
    expect(
      encodeTypedDomain({ domain, types: { EIP712Domain: declared } })
    ).toBe(abi.encode(["uint256", "string"], [1, "x"]))
  })
})

describe("toAbiTypes", () => {
  it("rejects recursive types instead of expanding them forever", () => {
    const types = {
      Root: [{ name: "n", type: "Node" }],
      Node: [
        { name: "kids", type: "Node[]" },
        { name: "v", type: "uint256" },
      ],
    }
    expect(() => toAbiTypes({ types })).toThrow(/Recursive/)
  })
})
