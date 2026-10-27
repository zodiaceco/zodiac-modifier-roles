import { expect, it, suite } from "vitest"
import { processPermissions } from "./processPermissions"
import { Encoding, Clearance, ExecutionOptions, Operator } from "../types"

import { abiEncode } from "../abiEncode"
import { normalizeCondition } from "../condition"
import { PermissionSet } from "./types"

const DUMMY_COMP = (id: number) => ({
  paramType: Encoding.Static,
  operator: Operator.Custom,
  compValue: abiEncode(["uint256"], [id]),
})

suite("processPermissions()", () => {
  const AddressOne = "0x0000000000000000000000000000000000000001"
  const AddressTwo = "0x0000000000000000000000000000000000000002"

  it("throws error when one found", () => {
    expect(() =>
      processPermissions([
        { targetAddress: AddressOne },
        {
          targetAddress: AddressOne,
          send: true,
        },
      ])
    ).toThrowError()
  })

  it("processes allowed, wildcarded and conditional entries", () => {
    expect(
      processPermissions([
        { targetAddress: AddressOne },
        {
          targetAddress: AddressTwo,
          selector: "0x00000001",
        },
        {
          targetAddress: AddressTwo,
          selector: "0x00000002",
          condition: DUMMY_COMP(1),
        },
      ])
    ).to.deep.equal({
      targets: [
        {
          address: AddressOne,
          clearance: Clearance.Target,
          executionOptions: ExecutionOptions.None,
          functions: [],
        },
        {
          address: AddressTwo,
          clearance: Clearance.Function,
          executionOptions: ExecutionOptions.None,
          functions: [
            {
              selector: "0x00000001",
              executionOptions: ExecutionOptions.None,
              wildcarded: true,
              condition: undefined,
            },
            {
              selector: "0x00000002",
              executionOptions: ExecutionOptions.None,
              wildcarded: false,
              condition: normalizeCondition(DUMMY_COMP(1)),
            },
          ],
        },
      ],
      annotations: [],
    })
  })

  it("finds and plucks annotations, returns only unique", () => {
    const permissionSet1: PermissionSet = [
      { targetAddress: AddressOne },
    ] as PermissionSet

    const permissionSet2: PermissionSet = [
      { targetAddress: AddressTwo },
    ] as PermissionSet

    const permissionSet3: PermissionSet = [
      { targetAddress: AddressOne },
    ] as PermissionSet

    permissionSet1.annotation = { uri: "uri-1", schema: "doesnt matter" }
    permissionSet2.annotation = { uri: "uri-2", schema: "doesnt matter" }
    permissionSet3.annotation = { uri: "uri-1", schema: "doesnt matter" }

    expect(
      processPermissions([permissionSet1, permissionSet2, permissionSet3])
    ).to.deep.equal({
      targets: [
        {
          address: AddressOne,
          clearance: Clearance.Target,
          executionOptions: ExecutionOptions.None,
          functions: [],
        },
        {
          address: AddressTwo,
          clearance: Clearance.Target,
          executionOptions: ExecutionOptions.None,
          functions: [],
        },
      ],
      annotations: [
        { uri: "uri-1", schema: "doesnt matter" },
        { uri: "uri-2", schema: "doesnt matter" },
      ],
    })
  })
})
