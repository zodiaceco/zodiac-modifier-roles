import { describe, expect, it } from "vitest"

import { Encoding, Operator } from "../types"
import { checkStoredConditions } from "./checkStored"
import { flattenCondition } from "./flattenCondition"
import { ConditionV2, migrateConditionV2 } from "./migrateV2"

const word = "0x" + "00".repeat(31) + "07"
const key = "0x" + "4b".repeat(32)
// v2 codes
const calldata = (...children: ConditionV2[]): ConditionV2 => ({
  paramType: 5,
  operator: 5,
  children,
})
const eq = (paramType = 1, compValue = word): ConditionV2 => ({
  paramType,
  operator: 16,
  compValue,
})
const pass = (paramType = 1, children?: ConditionV2[]): ConditionV2 => ({
  paramType,
  operator: 0,
  children,
})
const callAllowance: ConditionV2 = {
  paramType: 0,
  operator: 30,
  compValue: key,
}
const etherAllowance: ConditionV2 = {
  paramType: 0,
  operator: 29,
  compValue: key,
}

const stored = (c: ConditionV2) => {
  const v3 = migrateConditionV2(c)
  expect(checkStoredConditions(flattenCondition(v3) as any)).toBeDefined()
  return v3
}

describe("migrateConditionV2", () => {
  it("maps Calldata to AbiEncoded with the default 4 leading bytes", () => {
    expect(stored(calldata(eq(), pass()))).toEqual({
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Static,
          operator: Operator.EqualTo,
          compValue: word,
        },
        { paramType: Encoding.Static, operator: Operator.Pass },
      ],
    })
  })

  it("maps v2 AbiEncoded to AbiEncoded without leading bytes", () => {
    const v3 = stored(calldata({ paramType: 6, operator: 5, children: [eq()] }))
    expect(v3.children![0]).toMatchObject({
      paramType: Encoding.AbiEncoded,
      compValue: "0x0000",
    })
  })

  it("moves CallWithinAllowance out of the Matches", () => {
    expect(stored(calldata(eq(), callAllowance))).toEqual({
      paramType: Encoding.None,
      operator: Operator.And,
      children: [
        {
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue: word,
            },
          ],
        },
        {
          paramType: Encoding.None,
          operator: Operator.CallWithinAllowance,
          compValue: key,
        },
      ],
    })
  })

  it("turns EtherWithinAllowance into WithinAllowance on EtherValue", () => {
    const v3 = stored(calldata(eq(), etherAllowance))
    expect(v3.children![1]).toEqual({
      paramType: Encoding.EtherValue,
      operator: Operator.WithinAllowance,
      compValue: key,
    })
  })

  it("keeps only the allowance for a function without parameters", () => {
    expect(stored(calldata(callAllowance))).toEqual({
      paramType: Encoding.None,
      operator: Operator.CallWithinAllowance,
      compValue: key,
    })
  })

  it("drops Pass on None", () => {
    const v3 = stored(calldata(eq(), pass(0)))
    expect(v3.children).toHaveLength(1)
  })

  it("replaces the children of a Pass by type descriptions", () => {
    const tuple = pass(3, [
      { paramType: 0, operator: 2, children: [eq(), eq()] },
      pass(2),
    ])
    const v3 = stored(calldata(eq(), tuple))
    expect(v3.children![1]).toEqual({
      paramType: Encoding.Tuple,
      operator: Operator.Pass,
      children: [
        { paramType: Encoding.Static, operator: Operator.Pass },
        { paramType: Encoding.Dynamic, operator: Operator.Pass },
      ],
    })
  })

  it("turns a root Pass into no restriction", () => {
    expect(stored(pass(5, [pass(0)]))).toEqual({
      paramType: Encoding.None,
      operator: Operator.Pass,
    })
  })

  it("rejects what v3 cannot express", () => {
    expect(() =>
      migrateConditionV2(
        calldata({ paramType: 0, operator: 3, children: [eq()] })
      )
    ).toThrow(/Nor/)
    expect(() =>
      migrateConditionV2(
        calldata({ paramType: 4, operator: 8, children: [eq()] })
      )
    ).toThrow(/ArraySubset/)
    // v2 drops the offset word and hashes the rest: this never passes
    expect(() => migrateConditionV2(calldata(eq(2, word)))).toThrow(
      /never passes/
    )
  })
})
