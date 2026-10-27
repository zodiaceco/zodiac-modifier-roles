import { it, describe, expect } from "vitest"
import { allowCowOrderSigning } from "./allowCowOrderSigning"
import {
  encodeKey,
  processPermissions,
  targetIntegrity,
} from "zodiac-roles-sdk"
import { SupportedChainId } from "./types"

const WETH = "0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2" as const
const COW = "0xDEf1CA1fb7FBcDC777520aa7f396b4E015F497aB" as const

describe("allowCowOrderSigning", () => {
  it("throws on an empty sell or buy list, which would leave the token unrestricted", () => {
    expect(() =>
      allowCowOrderSigning({
        chainId: SupportedChainId.MAINNET,
        sell: [],
        buy: [COW],
      })
    ).toThrow("at least one token")
    expect(() =>
      allowCowOrderSigning({
        chainId: SupportedChainId.MAINNET,
        sell: [WETH],
        buy: [],
      })
    ).toThrow("at least one token")
  })

  it("should return valid permissions", () => {
    const permissions = allowCowOrderSigning({
      chainId: SupportedChainId.MAINNET,
      sell: [WETH],
      buy: [COW],
    })

    const { targets } = processPermissions(permissions)
    expect(() => targetIntegrity(targets)).not.toThrow()
  })

  it("should add WETH deposit permission when selling native token", () => {
    const permissions = allowCowOrderSigning({
      chainId: SupportedChainId.MAINNET,
      sell: ["native"],
      buy: [COW],
    })

    const depositPermission = permissions.find(
      (p) =>
        p.targetAddress === WETH &&
        "signature" in p &&
        p.signature === "deposit()" &&
        p.send === true
    )
    expect(depositPermission).toBeDefined()

    const { targets } = processPermissions(permissions)
    expect(() => targetIntegrity(targets)).not.toThrow()
  })

  it("should add WETH withdraw permission when buying native token", () => {
    const permissions = allowCowOrderSigning({
      chainId: SupportedChainId.MAINNET,
      sell: [COW],
      buy: ["native"],
    })

    const withdrawPermission = permissions.find(
      (p) =>
        p.targetAddress === WETH &&
        "signature" in p &&
        p.signature === "withdraw(uint256)"
    )
    expect(withdrawPermission).toBeDefined()

    const { targets } = processPermissions(permissions)
    expect(() => targetIntegrity(targets)).not.toThrow()
  })

  it("should add both deposit and withdraw permissions when native is in both sell and buy arrays with other tokens", () => {
    const permissions = allowCowOrderSigning({
      chainId: SupportedChainId.MAINNET,
      sell: ["native", COW],
      buy: ["native", COW],
    })

    const depositPermission = permissions.find(
      (p) =>
        p.targetAddress === WETH &&
        "signature" in p &&
        p.signature === "deposit()" &&
        p.send === true
    )
    const withdrawPermission = permissions.find(
      (p) =>
        p.targetAddress === WETH &&
        "signature" in p &&
        p.signature === "withdraw(uint256)"
    )
    expect(depositPermission).toBeDefined()
    expect(withdrawPermission).toBeDefined()

    const { targets } = processPermissions(permissions)
    expect(() => targetIntegrity(targets)).not.toThrow()
  })

  it("should skip signOrder, approve, and unsignOrder permissions when both sell and buy are only native/wrapped native tokens", () => {
    // Test case: native to WETH
    const permissionsNativeToWeth = allowCowOrderSigning({
      chainId: SupportedChainId.MAINNET,
      sell: ["native"],
      buy: [WETH],
    })

    // Should only have deposit, no signOrder/approve/unsignOrder
    expect(permissionsNativeToWeth).toHaveLength(1)
    expect(
      "signature" in permissionsNativeToWeth[0] &&
        permissionsNativeToWeth[0].signature
    ).toBe("deposit()")

    // Test case: WETH to native
    const permissionsWethToNative = allowCowOrderSigning({
      chainId: SupportedChainId.MAINNET,
      sell: [WETH],
      buy: ["native"],
    })

    // Should only have withdraw, no signOrder/approve/unsignOrder
    expect(permissionsWethToNative).toHaveLength(1)
    expect(
      "signature" in permissionsWethToNative[0] &&
        permissionsWethToNative[0].signature
    ).toBe("withdraw(uint256)")
  })

  it("should still include signOrder/approve/unsignOrder when mixed with other tokens", () => {
    // If sell includes both native and another token, should still have full permissions
    const permissions = allowCowOrderSigning({
      chainId: SupportedChainId.MAINNET,
      sell: ["native", COW],
      buy: [WETH],
    })

    const signOrderPermission = permissions.find(
      (p) => "signature" in p && p.signature.includes("signOrder")
    )
    const approvePermission = permissions.find(
      (p) => "signature" in p && p.signature === "approve(address,uint256)"
    )
    const unsignOrderPermission = permissions.find(
      (p) => "signature" in p && p.signature.includes("unsignOrder")
    )

    expect(signOrderPermission).toBeDefined()
    expect(approvePermission).toBeDefined()
    expect(unsignOrderPermission).toBeDefined()
  })

  it("should throw when sell and buy are identical single-element arrays", () => {
    // WETH to WETH
    expect(() =>
      allowCowOrderSigning({
        chainId: SupportedChainId.MAINNET,
        sell: [WETH],
        buy: [WETH],
      })
    ).toThrow("Cannot swap a token into itself")

    // native to native (both resolve to WETH)
    expect(() =>
      allowCowOrderSigning({
        chainId: SupportedChainId.MAINNET,
        sell: ["native"],
        buy: ["native"],
      })
    ).toThrow("Cannot swap a token into itself")

    // Should NOT throw when arrays have multiple elements even if overlapping
    expect(() =>
      allowCowOrderSigning({
        chainId: SupportedChainId.MAINNET,
        sell: [WETH, COW],
        buy: [WETH, COW],
      })
    ).not.toThrow()
  })

  it("should work with different chains", () => {
    const permissions = allowCowOrderSigning({
      chainId: SupportedChainId.GNOSIS_CHAIN,
      sell: ["native"],
      buy: [COW],
    })

    const WXDAI = "0xe91D153E0b41518A2Ce8Dd3D7944Fa863463a97d" as const
    const depositPermission = permissions.find(
      (p) =>
        p.targetAddress.toLowerCase() === WXDAI.toLowerCase() &&
        "signature" in p &&
        p.signature === "deposit()" &&
        p.send === true
    )
    expect(depositPermission).toBeDefined()

    const { targets } = processPermissions(permissions)
    expect(() => targetIntegrity(targets)).not.toThrow()
  })
})

describe("allowance keys", () => {
  it("accepts a label wherever an encoded key is accepted", () => {
    const options = {
      chainId: SupportedChainId.MAINNET,
      sell: [WETH],
      buy: [COW],
    }

    expect(
      processPermissions(
        allowCowOrderSigning({ ...options, sellAllowance: "usdc_payouts" })
      ).targets
    ).toEqual(
      processPermissions(
        allowCowOrderSigning({
          ...options,
          sellAllowance: encodeKey("usdc_payouts"),
        })
      ).targets
    )
  })
})
