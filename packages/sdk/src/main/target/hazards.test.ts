import { describe, expect, it } from "vitest"
import { AbiCoder, keccak256 } from "ethers"

import { allowPersonalSign, allowSignTypedMessage } from "../eip712-signer"
import { c } from "./authoring"
import { processPermissions } from "../permission"
import { permissionHazards } from "./hazards"
import { SIGN_TYPED_MESSAGE_LIB_ADDRESS } from "../addresses"

const LIB = SIGN_TYPED_MESSAGE_LIB_ADDRESS
const ROLES = "0x00000000000000000000000000000000000000aa"
const OTHER = "0x00000000000000000000000000000000000000bb"

const kinds = (permissions: readonly any[]) =>
  permissionHazards(processPermissions(permissions).targets, {
    rolesModifier: ROLES,
  }).map((h) => h.kind)

const types = {
  EIP712Domain: [
    { name: "chainId", type: "uint256" },
    { name: "verifyingContract", type: "address" },
  ],
  Order: [{ name: "amount", type: "uint256" }],
} as const

describe("permissionHazards", () => {
  it("flags signMessage unless exact messages are pinned", () => {
    const hash = keccak256("0x1234")
    const msg = (condition?: any) => ({
      targetAddress: LIB,
      signature: "signMessage(bytes)",
      delegatecall: true,
      condition,
    })
    expect(kinds([msg()])).toEqual(["sign-message"])
    expect(
      kinds([
        msg(
          c.calldataMatches(
            [c.bitmask({ mask: "0xff", value: "0x12" })],
            ["bytes"]
          )
        ),
      ])
    ).toEqual(["sign-message"])
    expect(kinds([msg(c.calldataMatches([hash], ["bytes"]))])).toEqual([])
    // a Matches with other leading bytes reads another block
    const pinnedElsewhere = c.calldataMatches([hash], ["bytes"])() as any
    expect(kinds([msg({ ...pinnedElsewhere, compValue: "0x0024" })])).toEqual([
      "sign-message",
    ])
    // pinning the offset word of the bytes pins nothing of the message
    expect(kinds([msg(c.calldataMatches([32n], ["uint256"]))])).toEqual([
      "sign-message",
    ])
    expect(
      kinds([
        msg(c.calldataMatches([c.or(hash, keccak256("0x5678"))], ["bytes"])),
      ])
    ).toEqual([])
  })

  it("accepts the SDK's typed-message and personal_sign permissions with a domain", () => {
    expect(
      kinds([
        allowSignTypedMessage({
          types,
          domain: { chainId: 1n, verifyingContract: OTHER },
          message: { amount: 1n },
        }),
        allowPersonalSign({ startsWith: "example.com wants you" }),
      ])
    ).toEqual([])
  })

  it("flags a typed-message permission with an open domain", () => {
    expect(
      kinds([
        allowSignTypedMessage({
          types,
          domain: c.pass,
          message: { amount: 1n },
        }),
      ])
    ).toEqual(["sign-typed-message-domain"])
  })

  it("flags a typed-message selector that does not pin the types", () => {
    const p = allowSignTypedMessage({
      types,
      domain: { chainId: 1n },
      message: { amount: 1n },
    })
    expect(kinds([{ ...p, condition: undefined }])).toEqual([
      "sign-typed-message-types",
    ])
    // an Or with one branch that leaves the types open
    expect(
      kinds([
        {
          ...p,
          condition: c.or(
            () => p.condition,
            () => ({
              ...p.condition,
              children: p.condition.children!.slice(0, 2).concat({
                paramType: 4,
                operator: 0,
                children: p.condition.children![2].children,
              }),
            })
          )(undefined as any),
        },
      ])
    ).toEqual(["sign-typed-message-types"])
  })

  it("flags delegatecall to a whole target and to other targets' functions", () => {
    expect(kinds([{ targetAddress: LIB, delegatecall: true }])).toEqual([
      "delegatecall-target",
    ])
    expect(
      kinds([
        { targetAddress: OTHER, signature: "f()", delegatecall: true },
        { targetAddress: OTHER, signature: "g()" },
      ])
    ).toEqual(["delegatecall-function"])
  })

  it("flags calls to the Roles Modifier itself", () => {
    expect(
      kinds([
        {
          targetAddress: ROLES,
          signature:
            "setAllowance(bytes32,uint128,uint128,uint128,uint64,uint64)",
        },
      ])
    ).toEqual(["roles-modifier"])
  })

  it("ignores permissions without delegatecall", () => {
    expect(
      kinds([
        {
          targetAddress: LIB,
          signature: "signMessage(bytes)",
          condition: c.calldataMatches(
            [AbiCoder.defaultAbiCoder().encode(["uint256"], [1])],
            ["bytes"]
          ),
        },
      ])
    ).toEqual([])
  })

  it("flags a domain with only chainId pinned, or an Or branch that leaves it open", () => {
    expect(
      kinds([
        allowSignTypedMessage({
          types,
          domain: { chainId: 1n },
          message: { amount: 1n },
        }),
      ])
    ).toEqual(["sign-typed-message-domain"])

    const isolated = allowSignTypedMessage({
      types,
      domain: { chainId: 1n, verifyingContract: OTHER },
      message: { amount: 1n },
    })
    const open = allowSignTypedMessage({
      types,
      domain: c.pass,
      message: { amount: 1n },
    })
    expect(kinds([isolated, { ...open, condition: open.condition }])).toEqual([
      "sign-typed-message-domain",
    ])
  })

  it("flags a domain without chainId", () => {
    expect(
      kinds([
        allowSignTypedMessage({
          types: {
            EIP712Domain: [{ name: "verifyingContract", type: "address" }],
            Order: [{ name: "amount", type: "uint256" }],
          } as const,
          domain: { verifyingContract: OTHER },
          message: { amount: 1n },
        }),
      ])
    ).toEqual(["sign-typed-message-domain"])
  })

  it("flags a domain without verifyingContract", () => {
    expect(
      kinds([
        allowSignTypedMessage({
          types: {
            EIP712Domain: [
              { name: "name", type: "string" },
              { name: "chainId", type: "uint256" },
            ],
            Order: [{ name: "amount", type: "uint256" }],
          } as const,
          domain: { name: "App", chainId: 1n },
          message: { amount: 1n },
        }),
      ])
    ).toEqual(["sign-typed-message-domain"])
  })

  it("flags typed messages that authorize the avatar elsewhere", () => {
    const roleTx = allowSignTypedMessage({
      types: {
        EIP712Domain: [
          { name: "chainId", type: "uint256" },
          { name: "verifyingContract", type: "address" },
        ],
        RoleTx: [
          { name: "to", type: "address" },
          { name: "value", type: "uint256" },
          { name: "data", type: "bytes" },
          { name: "operation", type: "uint8" },
          { name: "roleKey", type: "bytes32" },
          { name: "shouldRevert", type: "bool" },
          { name: "salt", type: "bytes32" },
        ],
      } as const,
      domain: { chainId: 1n, verifyingContract: OTHER },
      message: c.pass as any,
    })
    expect(permissionHazards(processPermissions([roleTx]).targets)).toEqual([
      expect.objectContaining({
        kind: "sign-typed-message-authority",
        message: expect.stringContaining("RoleTx"),
      }),
    ])

    const safeTx = allowSignTypedMessage({
      types: {
        EIP712Domain: [
          { name: "chainId", type: "uint256" },
          { name: "verifyingContract", type: "address" },
        ],
        SafeTx: [
          { name: "to", type: "address" },
          { name: "value", type: "uint256" },
          { name: "data", type: "bytes" },
          { name: "operation", type: "uint8" },
          { name: "safeTxGas", type: "uint256" },
          { name: "baseGas", type: "uint256" },
          { name: "gasPrice", type: "uint256" },
          { name: "gasToken", type: "address" },
          { name: "refundReceiver", type: "address" },
          { name: "nonce", type: "uint256" },
        ],
      } as const,
      domain: { chainId: 1n, verifyingContract: OTHER },
      message: c.pass as any,
    })
    expect(kinds([safeTx])).toEqual(["sign-typed-message-authority"])
  })
})
