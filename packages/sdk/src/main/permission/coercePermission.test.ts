import { expect, it, suite } from "vitest"
import { Operator, Encoding } from "../types"

import { abiEncode } from "../abiEncode"
import { coercePermission } from "./coercePermission"

const DUMMY_COMP = (id: number) => ({
  paramType: Encoding.Static,
  operator: Operator.Custom,
  compValue: abiEncode(["uint256"], [id]),
})

suite("coercePermission()", () => {
  const AddressOne = "0x0000000000000000000000000000000000000001"

  it("lowercases address", () => {
    expect(
      coercePermission({
        targetAddress: "0xABCDABCDABCDABCDABCDABCDABCDABCDABCDABCD",
      })
    ).to.deep.equal({
      targetAddress: "0xabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd",
      send: false,
      delegatecall: false,
    })
  })

  it("coerces signature into selector", () => {
    const signature1 = "balanceOf(address)"
    const signature2 =
      "function balanceOf(address owner) external view returns (uint256 balance)"
    const signature3 = "function balanceOf(address) external view"

    const p1 = coercePermission({
      targetAddress: AddressOne,
      signature: signature1,
    })
    const p2 = coercePermission({
      targetAddress: AddressOne,
      signature: signature2,
    })
    const p3 = coercePermission({
      targetAddress: AddressOne,
      signature: signature3,
    })

    const p4 = coercePermission({
      targetAddress: AddressOne,
      signature: "powerOf(address)",
    })

    expect(p1).to.deep.equal(p2)
    expect(p1).to.deep.equal(p2)
    expect(p1).to.deep.equal(p3)
    expect(p1.selector).to.deep.equal("0x70a08231")
    expect(p1.selector).to.not.equal(p4.selector)
  })

  it("passes conditions through", () => {
    expect(
      coercePermission({
        targetAddress: AddressOne,
        condition: DUMMY_COMP(222),
      })
    ).to.deep.equal({
      targetAddress: AddressOne,
      condition: DUMMY_COMP(222),
      send: false,
      delegatecall: false,
    })

    expect(
      coercePermission({
        targetAddress: AddressOne,
        condition: undefined,
      })
    ).to.deep.equal({
      targetAddress: AddressOne,
      condition: undefined,
      send: false,
      delegatecall: false,
    })
  })

  it("invokes condition function if one is provided", () => {
    expect(
      coercePermission({
        targetAddress: AddressOne,
        condition: () => DUMMY_COMP(12345),
      })
    ).to.deep.equal({
      targetAddress: AddressOne,
      condition: DUMMY_COMP(12345),
      send: false,
      delegatecall: false,
    })
  })

  it("coerces executionOptions flags", () => {
    expect(
      coercePermission({
        targetAddress: AddressOne,
        send: true,
      })
    ).to.deep.equal({
      targetAddress: AddressOne,
      send: true,
      delegatecall: false,
    })

    expect(
      coercePermission({
        targetAddress: AddressOne,
        delegatecall: true,
      })
    ).to.deep.equal({
      targetAddress: AddressOne,
      send: false,
      delegatecall: true,
    })
  })

  it("extraneous fields are kept out", () => {
    expect(
      coercePermission({
        targetAddress: AddressOne,
        hello: true,
      })
    ).to.deep.equal({
      targetAddress: AddressOne,
      send: false,
      delegatecall: false,
    })
  })
})
