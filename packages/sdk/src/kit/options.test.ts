import { expect, test } from "vitest"
import { c, encodeKey } from "zodiac-roles-sdk"
import { Condition, Encoding, Operator } from "../main/types"

import { allow } from "./typings"
import { checkRootConditionIntegrity } from "../main/condition/conditionIntegrity"

test("callWithinAllowance sets correct compValue", () => {
  const allowanceKey =
    "0x0000000000000000000000000000000000000000000000000000000000000001" as `0x${string}`

  // Use any allow kit function — they all go through applyOptions
  const permission = allow.mainnet.lido.stETH.submit(c.pass, {
    callWithinAllowance: allowanceKey,
  })

  // The condition tree should contain a CallWithinAllowance node
  // with compValue equal to the provided allowance key
  expect(permission.condition).toBeDefined()

  const condition = permission.condition as Condition
  const callWithinAllowanceNode = condition.children?.find(
    (child) => child.operator === Operator.CallWithinAllowance
  )

  expect(callWithinAllowanceNode).toBeDefined()
  expect(callWithinAllowanceNode!.paramType).toBe(Encoding.None)
  expect(callWithinAllowanceNode!.compValue).toBe(allowanceKey)

  // The condition should pass the SDK's own integrity check
  expect(() => checkRootConditionIntegrity(condition)).not.toThrow()
})

test("callWithinAllowance without etherWithinAllowance does not throw", () => {
  const allowanceKey =
    "0x00000000000000000000000000000000000000000000000000000000deadbeef" as `0x${string}`

  // This was the exact scenario that triggered the bug:
  // passing callWithinAllowance WITHOUT etherWithinAllowance caused
  // compValue to be undefined (it read options.etherWithinAllowance by mistake)
  expect(() => {
    const permission = allow.mainnet.lido.stETH.submit(c.pass, {
      callWithinAllowance: allowanceKey,
    })
    checkRootConditionIntegrity(permission.condition as Condition)
  }).not.toThrow()
})

test("allowance options accept a plain label", () => {
  const withLabel = allow.mainnet.lido.stETH.submit(c.pass, {
    callWithinAllowance: "my-call-allowance",
  })
  const withEncodedKey = allow.mainnet.lido.stETH.submit(c.pass, {
    callWithinAllowance: encodeKey("my-call-allowance"),
  })

  expect(withLabel.condition).toEqual(withEncodedKey.condition)
})

test("callWithinAllowance goes next to the Matches, which v3 requires", () => {
  const permission = allow.mainnet.lido.stETH.submit(c.pass, {
    callWithinAllowance: "calls",
  })
  const condition = permission.condition as Condition
  expect(condition.operator).toBe(Operator.And)
  expect(condition.children![0].operator).toBe(Operator.Matches)
  expect(
    condition.children![0].children!.some(
      (child) => child.operator === Operator.CallWithinAllowance
    )
  ).toBe(false)
})

test("callWithinAllowance without scopings is the allowance alone", () => {
  const permission = allow.mainnet.lido.stETH.submit(undefined, {
    callWithinAllowance: "calls",
  })
  expect(permission.condition).toEqual({
    paramType: Encoding.None,
    operator: Operator.CallWithinAllowance,
    compValue: encodeKey("calls"),
  })
})

test("falsy values are scopings, not wildcards", () => {
  const permission = allow.mainnet.lido.stETH.approve(undefined, 0)
  const condition = permission.condition as Condition
  expect(condition).toBeDefined()
  expect(condition.children![1].operator).toBe(Operator.EqualTo)
})

test("throws on more arguments than scopings and options", () => {
  expect(() =>
    (allow.mainnet.lido.stETH.submit as any)(undefined, {}, {})
  ).toThrow("got 3 arguments")
  expect(() => (allow.mainnet.lido.stETH.submit as any)(undefined, 5)).toThrow(
    "options object"
  )
})
