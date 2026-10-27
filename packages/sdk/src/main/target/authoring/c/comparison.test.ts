import { describe, expect, it } from "vitest"
import { ParamType } from "ethers"
import { Encoding, Operator } from "../../../types"

import { bitmask, gt, gte, lt, lte } from "./comparison"
import { avatarIsOwnerOfErc721 } from "./custom"

const t = (type: string) => ParamType.from(type)

describe("bitmask", () => {
  it("encodes mask and value at their own length (v3 format)", () => {
    expect(
      bitmask({ shift: 3, mask: "0xffff", value: "0xaabb" })(t("bytes"))
    ).toEqual({
      paramType: Encoding.Dynamic,
      operator: Operator.Bitmask,
      compValue: "0x0003ffffaabb",
    })
  })

  it("pads the shorter of mask and value to the longer", () => {
    expect(
      bitmask({ mask: "0xffffff", value: "0x12" })(t("bytes32")).compValue
    ).toBe("0x0000ffffff120000")
  })

  it("supports masks longer than 15 bytes", () => {
    const mask = "0x" + "ff".repeat(20)
    const value = "0x" + "ab".repeat(20)
    expect(bitmask({ mask, value })(t("bytes")).compValue).toBe(
      "0x0000" + "ff".repeat(20) + "ab".repeat(20)
    )
  })

  it("rejects a value with bits outside the mask (never passes)", () => {
    expect(() => bitmask({ mask: "0xf0", value: "0x0f" })(t("bytes"))).toThrow(
      "never passes"
    )
    expect(() =>
      bitmask({ mask: "0xff", value: "0x1234" })(t("bytes"))
    ).toThrow("never passes")
  })

  it("rejects a window beyond a static value's 32 bytes", () => {
    expect(() =>
      bitmask({ shift: 30, mask: "0xffffff", value: "0x000000" })(t("uint256"))
    ).toThrow("never passes")
    expect(() =>
      bitmask({ shift: 29, mask: "0xffffff", value: "0x000000" })(t("uint256"))
    ).not.toThrow()
  })

  it("rejects an empty mask and a bad shift", () => {
    expect(() => bitmask({ mask: "0x", value: "0x" })(t("bytes"))).toThrow(
      "empty"
    )
    expect(() =>
      bitmask({ shift: 65536, mask: "0xff", value: "0x00" })(t("bytes"))
    ).toThrow("shift")
    expect(() =>
      bitmask({ shift: 1.5, mask: "0xff", value: "0x00" })(t("bytes"))
    ).toThrow("shift")
  })
})

describe("gt / gte / lt / lte", () => {
  it("gte at the type's minimum always passes: a Pass", () => {
    expect(gte(0)(t("uint256"))).toEqual({
      paramType: Encoding.Static,
      operator: Operator.Pass,
    })
    expect(gte(-128)(t("int8")).operator).toBe(Operator.Pass)
  })

  it("lte at the type's maximum always passes: a Pass", () => {
    expect(lte((1n << 256n) - 1n)(t("uint256")).operator).toBe(Operator.Pass)
    expect(lte(255)(t("uint8")).operator).toBe(Operator.Pass)
  })

  it("rejects bounds that never pass", () => {
    expect(() => gt(255)(t("uint8"))).toThrow("never passes")
    expect(() => lt(0)(t("uint256"))).toThrow("never passes")
    expect(() => lt(-128)(t("int8"))).toThrow("never passes")
  })

  it("rejects bounds outside the type", () => {
    expect(() => gt(256)(t("uint8"))).toThrow("out of range")
    expect(() => gte(-1)(t("uint256"))).toThrow("out of range")
    expect(() => lte(128)(t("int8"))).toThrow("out of range")
  })

  it("still builds the comparison otherwise", () => {
    expect(gte(5)(t("uint256")).operator).toBe(Operator.GreaterThan)
    expect(lte(-5)(t("int256")).operator).toBe(Operator.SignedIntLessThan)
  })
})

describe("avatarIsOwnerOfErc721", () => {
  it("throws until the v3 checker is deployed", () => {
    expect(() => avatarIsOwnerOfErc721(t("uint256"))).toThrow("not deployed")
  })
})
