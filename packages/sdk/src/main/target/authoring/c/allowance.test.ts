import { describe, expect, it } from "vitest"
import { ParamType } from "ethers"

import { abiEncode } from "../../../abiEncode"
import { encodeKey } from "../../../keys"
import { withinAllowance } from "./allowance"

const uint256 = ParamType.from("uint256")

describe("withinAllowance", () => {
  it("accepts an allowance key as a label", () => {
    expect(withinAllowance("test-allowance")(uint256)).toHaveProperty(
      "compValue",
      abiEncode(["bytes32"], [encodeKey("test-allowance")])
    )
  })

  it("encodes a label and an already encoded key to the same condition", () => {
    expect(withinAllowance("test-allowance")(uint256)).toEqual(
      withinAllowance(encodeKey("test-allowance"))(uint256)
    )
  })

  it("rejects a key too long to pack into bytes32", () => {
    expect(() => withinAllowance("a".repeat(32))(uint256)).toThrow(
      "at most 31 bytes"
    )
  })
})

describe("withinAllowance with a conversion", () => {
  const key = encodeKey("test-allowance")
  const adapter = "0x" + "ab".repeat(20)

  it("packs key, balance decimals and input decimals", () => {
    expect(
      withinAllowance("test-allowance", {
        balanceDecimals: 6,
        inputDecimals: 18,
      })(uint256).compValue
    ).toBe(key + "0612")
  })

  it("appends the adapter and its params", () => {
    expect(
      withinAllowance("test-allowance", {
        balanceDecimals: 18,
        inputDecimals: 8,
        priceAdapter: adapter as `0x${string}`,
        adapterParams: "0xdeadbeef",
      })(uint256).compValue
    ).toBe(key + "1208" + "ab".repeat(20) + "deadbeef")
  })

  it("rejects decimals the contract rejects", () => {
    expect(() =>
      withinAllowance("x", { balanceDecimals: 28, inputDecimals: 0 })(uint256)
    ).toThrow("from 0 to 27")
    expect(() =>
      withinAllowance("x", { balanceDecimals: 1.5, inputDecimals: 0 })(uint256)
    ).toThrow("from 0 to 27")
  })

  it("rejects adapter params without an adapter", () => {
    expect(() =>
      withinAllowance("x", {
        balanceDecimals: 0,
        inputDecimals: 0,
        adapterParams: "0x01",
      })(uint256)
    ).toThrow("require a `priceAdapter`")
  })
})
