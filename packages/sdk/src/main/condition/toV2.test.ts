import { describe, expect, it } from "vitest"
import { targetIntegrity as targetIntegrityV2 } from "zodiac-roles-sdk-v2"

import { c } from "../target/authoring"
import { processPermissions } from "../permission/processPermissions"
import {
  Clearance,
  Condition,
  Encoding,
  ExecutionOptions,
  Operator,
  Target,
} from "../types"
import { ConditionV2, migrateConditionV2 } from "./migrateV2"
import {
  IncompatibleWithV2Error,
  toConditionV2,
  toTargetsV2,
  v2Issues,
} from "./toV2"

const word = "0x" + "00".repeat(31) + "07"
const key = "0x" + "4b".repeat(32)
const target = "0x" + "11".repeat(20)

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
  ...(children ? { children } : {}),
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

const matches = (...children: Condition[]): Condition => ({
  paramType: Encoding.AbiEncoded,
  operator: Operator.Matches,
  children,
})
const static_: Condition = {
  paramType: Encoding.Static,
  operator: Operator.Pass,
}

/** Targets scoping one function with each permission, as v2 checks them. */
const appliedOnV2 = (
  ...permissions: Parameters<typeof processPermissions>[0]
) => {
  const { targets } = processPermissions(permissions)
  const v2 = toTargetsV2(targets)
  targetIntegrityV2(v2 as Parameters<typeof targetIntegrityV2>[0])
  return v2
}

describe("toConditionV2", () => {
  describe("undoes migrateConditionV2", () => {
    const v2Conditions: [string, ConditionV2][] = [
      ["calldata", calldata(eq(), pass())],
      [
        "nested AbiEncoded",
        calldata({ paramType: 6, operator: 5, children: [eq()] }),
      ],
      ["call allowance", calldata(eq(), callAllowance)],
      ["ether allowance", calldata(etherAllowance, eq())],
      [
        "or of calldata",
        {
          paramType: 0,
          operator: 2,
          children: [calldata(eq()), calldata(pass(), eq())],
        },
      ],
      [
        "arrays and tuples",
        calldata(
          {
            paramType: 4,
            operator: 6,
            children: [{ paramType: 3, operator: 5, children: [eq(), pass()] }],
          },
          { paramType: 4, operator: 7, children: [eq()] }
        ),
      ],
      [
        "comparisons",
        calldata(
          { paramType: 1, operator: 17, compValue: word },
          { paramType: 1, operator: 18, compValue: word },
          { paramType: 1, operator: 15 },
          { paramType: 1, operator: 28, compValue: key }
        ),
      ],
      [
        "a bitmask",
        calldata({
          paramType: 2,
          operator: 21,
          compValue:
            "0x0000" +
            "ff".repeat(4) +
            "00".repeat(11) +
            "12345678" +
            "00".repeat(11),
        }),
      ],
      [
        "EqualTo on a dynamic value",
        calldata(
          eq(
            2,
            "0x" +
              "00".repeat(31) +
              "20" +
              "00".repeat(31) +
              "02" +
              "ab".repeat(2) +
              "00".repeat(30)
          )
        ),
      ],
    ]

    it.each(v2Conditions)("%s", (_, v2) => {
      const v3 = migrateConditionV2(v2)
      expect(migrateConditionV2(toConditionV2(v3))).toEqual(v3)
    })

    it("restores v2's Calldata and AbiEncoded", () => {
      expect(
        toConditionV2(
          migrateConditionV2(
            calldata({ paramType: 6, operator: 5, children: [eq()] })
          )
        )
      ).toEqual(calldata({ paramType: 6, operator: 5, children: [eq()] }))
    })

    it("restores EtherWithinAllowance", () => {
      expect(
        toConditionV2({
          paramType: Encoding.EtherValue,
          operator: Operator.WithinAllowance,
          compValue: key as `0x${string}`,
        })
      ).toEqual(etherAllowance)
    })
  })

  describe("refuses what v2 cannot enforce", () => {
    it.each([
      Operator.Empty,
      Operator.ArrayTailMatches,
      Operator.ZipSome,
      Operator.ZipEvery,
      Operator.Slice,
      Operator.Pluck,
      Operator.WithinRatio,
    ])("operator %s", (operator) => {
      expect(
        v2Issues(matches(static_, { paramType: Encoding.None, operator }))
      ).toEqual([
        { message: `${Operator[operator]} is not available`, path: [1] },
      ])
    })

    it("conditions on the ether value other than an allowance", () => {
      expect(
        v2Issues({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            matches(static_),
            {
              paramType: Encoding.EtherValue,
              operator: Operator.LessThan,
              compValue: word as `0x${string}`,
            },
          ],
        })
      ).toEqual([
        { message: "LessThan on the ether value is not available", path: [1] },
      ])
    })

    it("allowances with a price adapter or converting decimals", () => {
      const allowance = (conversion: string): Condition =>
        matches({
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: `${key}${conversion}` as `0x${string}`,
        })
      expect(v2Issues(allowance("1212"))).toEqual([])
      expect(v2Issues(allowance("1206"))).toMatchObject([
        { message: "allowances converting between decimals are not available" },
      ])
      expect(v2Issues(allowance("1212" + "22".repeat(20)))).toMatchObject([
        { message: "allowances with a price adapter are not available" },
      ])
    })

    it("comparing leading bytes, or reading after other than 0 or 4", () => {
      expect(
        v2Issues({ ...matches(static_), compValue: "0x0004a9059cbb" })
      ).toMatchObject([{ message: expect.stringContaining("leading bytes") }])
      expect(v2Issues({ ...matches(static_), compValue: "0x0008" })).toEqual([
        { message: "8 leading bytes are not available, only 0 or 4", path: [] },
      ])
    })

    it("bitmasks wider than 15 bytes", () => {
      const bitmask = (mask: string, value: string): Condition =>
        matches({
          paramType: Encoding.Dynamic,
          operator: Operator.Bitmask,
          compValue: `0x0000${mask}${value}`,
        })
      expect(v2Issues(bitmask("ff".repeat(16), "00".repeat(16)))).toMatchObject(
        [{ message: "bitmasks are at most 15 bytes, this one is 16" }]
      )
      // trailing bytes the mask does not select check nothing
      expect(
        v2Issues(bitmask("ff".repeat(15) + "00".repeat(5), "00".repeat(20)))
      ).toEqual([])
    })

    it("custom conditions without a v2 checker", () => {
      expect(
        v2Issues(
          matches({
            paramType: Encoding.Static,
            operator: Operator.Custom,
            compValue: `0x${"22".repeat(20)}`,
          })
        )
      ).toMatchObject([
        { message: expect.stringContaining("has no known v2 checker") },
      ])
    })

    it("EqualTo on a non-inlined value with at most one word", () => {
      expect(
        v2Issues(
          matches({
            paramType: Encoding.Dynamic,
            operator: Operator.EqualTo,
            compValue: word as `0x${string}`,
          })
        )
      ).toMatchObject([{ message: expect.stringContaining("never passes") }])
    })

    it("lists every issue with its path", () => {
      expect(() =>
        toConditionV2(
          matches(
            {
              paramType: Encoding.Static,
              operator: Operator.Pluck,
              compValue: "0x00",
            },
            {
              paramType: Encoding.Array,
              operator: Operator.ArrayTailMatches,
              children: [static_],
            }
          )
        )
      ).toThrow(
        new IncompatibleWithV2Error([
          { message: "Pluck is not available", path: [0] },
          { message: "ArrayTailMatches is not available", path: [1] },
        ])
      )
    })
  })
})

describe("toTargetsV2", () => {
  it("passes v2's integrity checks for conditions built with c", () => {
    appliedOnV2(
      {
        targetAddress: target as `0x${string}`,
        signature: "transfer(address,uint256)",
        condition: c.calldataMatches(
          [c.avatar, c.withinAllowance("budget")],
          ["address", "uint256"]
        ),
      },
      {
        targetAddress: target as `0x${string}`,
        signature: "approve(address,uint256)",
        condition: c.calldataMatches(
          [c.avatar, c.lte(1000)],
          ["address", "uint256"],
          {
            callWithinAllowance: "calls",
          }
        ),
      },
      {
        targetAddress: target as `0x${string}`,
        signature: "flags(bytes)",
        condition: c.calldataMatches(
          [c.bitmask({ shift: 4, mask: "0xff00ff", value: "0x120034" })],
          ["bytes"]
        ),
      }
    )
  })

  it("leaves nested calldata to v2's own reading checks", () => {
    // v2's checks ask for an acknowledgement on nested calldata, which only
    // the author can give
    expect(() =>
      appliedOnV2({
        targetAddress: target as `0x${string}`,
        signature: "multicall(bytes[])",
        condition: c.calldataMatches(
          [
            c.every(
              c.or(
                c.calldataMatches([c.avatar], ["address"], {
                  selector: "0x12345678",
                }),
                c.calldataMatches([c.gt(1)], ["uint256"], {
                  selector: "0x87654321",
                })
              )
            ),
          ],
          ["bytes[]"]
        ),
      })
    ).toThrow("acknowledge this condition")
  })

  it("names the target and function of each issue", () => {
    const targets: Target[] = [
      {
        address: target as `0x${string}`,
        clearance: Clearance.Function,
        executionOptions: ExecutionOptions.None,
        functions: [
          {
            selector: "0xa9059cbb",
            executionOptions: ExecutionOptions.None,
            wildcarded: false,
            condition: matches({
              paramType: Encoding.Static,
              operator: Operator.Pluck,
              compValue: "0x00",
            }),
          },
        ],
      },
    ]
    expect(() => toTargetsV2(targets)).toThrow(
      `${target}.0xa9059cbb: Pluck is not available (at 0)`
    )
  })

  it("wildcards a function whose condition restricts nothing", () => {
    const [{ functions }] = toTargetsV2([
      {
        address: target as `0x${string}`,
        clearance: Clearance.Function,
        executionOptions: ExecutionOptions.None,
        functions: [
          {
            selector: "0xa9059cbb",
            executionOptions: ExecutionOptions.None,
            wildcarded: false,
            condition: { paramType: Encoding.None, operator: Operator.Pass },
          },
        ],
      },
    ])
    expect(functions).toEqual([
      {
        selector: "0xa9059cbb",
        executionOptions: ExecutionOptions.None,
        wildcarded: true,
      },
    ])
  })
})
