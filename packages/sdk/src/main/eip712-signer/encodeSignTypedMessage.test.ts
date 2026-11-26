import { describe, expect, it } from "vitest"
import { Interface, toUtf8Bytes, hexlify } from "ethers"

import {
  allowSignTypedMessage,
  encodePersonalSign,
  encodeSignTypedMessage,
} from "./index"

const domain = {
  name: "Mail",
  chainId: 1,
  verifyingContract: "0xCcCCccccCCCCcCCCCCCcCcCccCcCCCcCcccccccC",
} as const

const EIP712Domain = [
  { name: "name", type: "string" },
  { name: "chainId", type: "uint256" },
  { name: "verifyingContract", type: "address" },
] as const

const Person = [
  { name: "name", type: "string" },
  { name: "wallet", type: "address" },
] as const

const person = {
  name: "Bob",
  wallet: "0xbBbBBBBbbBBBbbbBbbBbbbbBBbBbbbbBbBbbBBbB",
} as const

describe("primaryType", () => {
  it("signs the named struct when another struct references it", () => {
    const bundle = {
      EIP712Domain,
      Person,
      Mail: [
        { name: "from", type: "Person" },
        { name: "contents", type: "string" },
      ],
    } as const

    const data = encodeSignTypedMessage({
      domain,
      types: bundle,
      primaryType: "Person",
      message: person,
    })
    const alone = encodeSignTypedMessage({
      domain,
      types: { EIP712Domain, Person },
      message: person,
    })
    expect(data).toBe(alone)

    const { selector } = allowSignTypedMessage({
      types: bundle,
      primaryType: "Person",
      domain: { chainId: 1n },
      message: { name: "Bob" },
    })
    expect(data.slice(0, 10)).toBe(selector)
  })

  it("drops types the primary type does not use", () => {
    const bundle = {
      EIP712Domain,
      Person,
      Unused: [{ name: "x", type: "uint256" }],
    } as const

    expect(
      encodeSignTypedMessage({
        domain,
        types: bundle,
        primaryType: "Person",
        message: person,
      })
    ).toBe(
      encodeSignTypedMessage({
        domain,
        types: { EIP712Domain, Person },
        message: person,
      })
    )
  })

  it("asks for primaryType when it cannot be inferred", () => {
    expect(() =>
      encodeSignTypedMessage({
        domain,
        types: {
          EIP712Domain,
          Person,
          Unused: [{ name: "x", type: "uint256" }],
        } as const,
        message: person as any,
      })
    ).toThrow(/candidates: Person, Unused\. Pass primaryType/)
  })

  it("rejects a primaryType not in types, or EIP712Domain", () => {
    const types = { EIP712Domain, Person } as const
    expect(() =>
      encodeSignTypedMessage({
        domain,
        types,
        primaryType: "Mail" as any,
        message: person as any,
      })
    ).toThrow(/not declared/)
    expect(() =>
      allowSignTypedMessage({
        types,
        // @ts-expect-error - the domain is not a message struct
        primaryType: "EIP712Domain",
        domain: { chainId: 1n },
        message: {} as any,
      })
    ).toThrow(/not EIP712Domain/)
  })

  it("rejects a primary type that references itself", () => {
    const types = {
      EIP712Domain,
      Node: [
        { name: "value", type: "uint256" },
        { name: "next", type: "Node[]" },
      ],
    } as const
    const recursive = /Recursive EIP-712 types are not supported: Node -> Node/

    expect(() =>
      encodeSignTypedMessage({
        domain,
        types,
        primaryType: "Node",
        message: { value: 1n, next: [] } as any,
      })
    ).toThrow(recursive)
    expect(() =>
      allowSignTypedMessage({
        types,
        primaryType: "Node",
        domain: { chainId: 1n },
        message: {} as any,
      })
    ).toThrow(recursive)
  })

  it("rejects a message struct that references EIP712Domain", () => {
    const withDomain = {
      EIP712Domain,
      Bad: [{ name: "d", type: "EIP712Domain" }],
    } as const
    const withoutDomain = {
      Bad: [{ name: "d", type: "EIP712Domain" }],
    } as const

    expect(() =>
      encodeSignTypedMessage({
        domain,
        types: withDomain,
        message: { d: { ...domain, chainId: 1n } },
      })
    ).toThrow(/must not reference EIP712Domain/)
    expect(() =>
      allowSignTypedMessage({
        types: withDomain,
        domain: { chainId: 1n },
        message: {} as any,
      })
    ).toThrow(/must not reference EIP712Domain/)
    expect(() =>
      encodeSignTypedMessage({
        domain,
        types: withoutDomain,
        primaryType: "Bad",
        message: { d: domain } as any,
      })
    ).toThrow(/must not reference EIP712Domain/)
  })

  it("types the message after primaryType", () => {
    const bundle = {
      EIP712Domain,
      Person,
      Mail: [
        { name: "from", type: "Person" },
        { name: "contents", type: "string" },
      ],
    } as const

    expect(() =>
      allowSignTypedMessage({
        types: bundle,
        primaryType: "Person",
        domain: { chainId: 1n },
        // @ts-expect-error - `contents` is a field of Mail, not Person
        message: { contents: "hi" },
      })
    ).toThrow(/unknown keys: contents/)
  })
})

describe("encodePersonalSign", () => {
  const iface = Interface.from(["function personalSign(bytes message)"])
  const signed = (data: string) =>
    iface.decodeFunctionData("personalSign", data)[0]

  it("signs a string as its UTF-8 text", () => {
    expect(signed(encodePersonalSign({ message: "0xdeadbeef" }))).toBe(
      hexlify(toUtf8Bytes("0xdeadbeef"))
    )
  })

  it("signs { raw } as the given bytes", () => {
    expect(signed(encodePersonalSign({ message: { raw: "0xdeadbeef" } }))).toBe(
      "0xdeadbeef"
    )
    expect(
      signed(encodePersonalSign({ message: { raw: new Uint8Array([1, 2]) } }))
    ).toBe("0x0102")
  })
})
