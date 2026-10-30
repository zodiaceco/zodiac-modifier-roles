import { expect, it, suite } from "vitest"
import { Encoding, Operator } from "../types"

import { abiEncode } from "../abiEncode"
import {
  checkConditionIntegrity,
  checkRootConditionIntegrity,
} from "./conditionIntegrity"
import { migrateConditionV2 } from "./migrateV2"

suite("checkConditionIntegrity()", () => {
  it("should throw for And without children", () => {
    expect(() =>
      checkConditionIntegrity({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [],
      })
    ).to.throw("`And` condition must have children")
  })

  it("should throw for EqualTo without compValue", () => {
    expect(() =>
      checkConditionIntegrity({
        paramType: Encoding.Static,
        operator: Operator.EqualTo,
      })
    ).to.throw("`EqualTo` condition must have a compValue")
  })

  it("should throw for And with compValue", () => {
    expect(() =>
      checkConditionIntegrity({
        paramType: Encoding.None,
        operator: Operator.And,
        compValue: abiEncode(["uint256"], [0]),
        children: [{ paramType: Encoding.Static, operator: Operator.Pass }],
      })
    ).to.throw("`And` condition cannot have a compValue")
  })

  it("leaves the types of And/Or children to the SDK check", () => {
    // which children fit together (prefixes of one tuple, interpretations
    // of one bytes value) is checkStored's rule, in any order
    for (const children of [
      [
        { paramType: Encoding.AbiEncoded, operator: Operator.Pass },
        { paramType: Encoding.Dynamic, operator: Operator.Pass },
      ],
      [
        { paramType: Encoding.Dynamic, operator: Operator.Pass },
        { paramType: Encoding.AbiEncoded, operator: Operator.Pass },
      ],
    ]) {
      expect(() =>
        checkConditionIntegrity({
          paramType: Encoding.None,
          operator: Operator.And,
          children,
        })
      ).to.not.throw()
    }
  })
})

suite("checkRootConditionIntegrity()", () => {
  it("should throw if the root param type is not AbiEncoded", () => {
    expect(() =>
      checkRootConditionIntegrity({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [{ paramType: Encoding.Static, operator: Operator.Pass }],
      })
    ).to.throw("Root param type must be `AbiEncoded`, got `Static`")
  })
})

suite("checkRootConditionIntegrity() with v3 operators", () => {
  const word = (n: number) =>
    `0x${n.toString(16).padStart(64, "0")}` as `0x${string}`
  const arrayOfUint = (operator: Operator, compValue?: `0x${string}`) => ({
    paramType: Encoding.Array,
    operator,
    compValue,
    children: [{ paramType: Encoding.Static, operator: Operator.Pass }],
  })

  it("accepts ArraySome and ArrayTailMatches (no longer banned)", () => {
    for (const operator of [Operator.ArraySome, Operator.ArrayTailMatches]) {
      expect(() =>
        checkRootConditionIntegrity({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [arrayOfUint(operator)],
        })
      ).not.toThrow()
    }
  })

  it("accepts Plucks with a Zip and an EtherValue check next to the calldata", () => {
    expect(() =>
      checkRootConditionIntegrity({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            compValue: "0x0004a9059cbb",
            children: [
              arrayOfUint(Operator.Pluck, "0x00"),
              arrayOfUint(Operator.Pluck, "0x01"),
            ],
          },
          {
            paramType: Encoding.None,
            operator: Operator.ZipEvery,
            compValue: "0x0001",
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.Matches,
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.EqualTo,
                    compValue: word(5),
                  },
                  { paramType: Encoding.Static, operator: Operator.Pass },
                ],
              },
            ],
          },
          {
            paramType: Encoding.EtherValue,
            operator: Operator.LessThan,
            compValue: word(10),
          },
        ],
      })
    ).not.toThrow()
  })

  it("requires a compValue on Pluck", () => {
    expect(() =>
      checkConditionIntegrity({
        paramType: Encoding.Static,
        operator: Operator.Pluck,
      })
    ).toThrow("must have a compValue")
  })

  it("accepts a Pass on None, as migrateConditionV2 makes of a v2 root Pass", () => {
    expect(() =>
      checkRootConditionIntegrity(
        migrateConditionV2({
          paramType: Encoding.None,
          operator: Operator.Pass,
        })
      )
    ).not.toThrow()
  })
})
