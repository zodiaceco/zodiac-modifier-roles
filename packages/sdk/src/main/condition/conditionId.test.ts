import { expect, it, suite } from "vitest"
import { Encoding, Operator } from "../types"

import { conditionAddress, conditionId } from "./conditionId"
import { normalizeCondition } from "./normalize"

suite("conditionAddress", () => {
  it("calculates the create2 storage address of the condition", () => {
    const normalizedCondition = normalizeCondition({
      operator: Operator.Matches,
      paramType: Encoding.AbiEncoded,
      children: [
        {
          operator: Operator.Matches,
          paramType: Encoding.Tuple,
          children: [
            {
              operator: Operator.EqualToAvatar,
              paramType: Encoding.Static,
            },
            {
              operator: Operator.EqualTo,
              paramType: Encoding.Dynamic,
              compValue:
                "0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000016617262697472756d666f756e646174696f6e2e65746800000000000000000000",
            },
            { operator: Operator.Pass, paramType: Encoding.Static },
            { operator: Operator.Pass, paramType: Encoding.Static },
            {
              operator: Operator.Pass,
              paramType: Encoding.Array,
              children: [
                { operator: Operator.Pass, paramType: Encoding.Static },
              ],
            },
            { operator: Operator.Pass, paramType: Encoding.Dynamic },
            {
              operator: Operator.EqualTo,
              paramType: Encoding.Dynamic,
              compValue:
                "0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000008736e617073686f74000000000000000000000000000000000000000000000000",
            },
          ],
        },
        {
          operator: Operator.Matches,
          paramType: Encoding.Tuple,
          children: [
            {
              operator: Operator.EqualTo,
              paramType: Encoding.Dynamic,
              compValue:
                "0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000008736e617073686f74000000000000000000000000000000000000000000000000",
            },
          ],
        },
      ],
    })
    expect(conditionAddress(normalizedCondition)).to.equal(
      "0xa835a51f2a581493b7416daed729cc78e0f68224"
    )
  })
})

suite("conditionId", () => {
  it("ignores field order, extra fields, missing children and hex case", () => {
    const a = {
      compValue: "0xABCD",
      operator: Operator.EqualTo,
      paramType: Encoding.Static,
      extra: true,
    } as any
    const b = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0xabcd",
      children: [],
    } as any
    expect(conditionId(a)).toBe(conditionId(b))
  })

  it("treats a missing compValue like an empty one", () => {
    expect(
      conditionId({ paramType: Encoding.Static, operator: Operator.Pass })
    ).toBe(
      conditionId({
        paramType: Encoding.Static,
        operator: Operator.Pass,
        compValue: "0x",
      })
    )
  })

  it("tells apart trees that differ only in how compValue bytes are split", () => {
    const twoChildren = {
      paramType: Encoding.Tuple,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Static,
          operator: Operator.EqualTo,
          compValue: "0x11",
        },
        { paramType: Encoding.Static, operator: Operator.Pass },
      ],
    } as const
    const oneChild = {
      paramType: Encoding.Tuple,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Static,
          operator: Operator.EqualTo,
          compValue: "0x110020",
        },
      ],
    } as const
    expect(conditionId(twoChildren)).not.toBe(conditionId(oneChild))

    const split = (first: `0x${string}`, second: `0x${string}`) => ({
      paramType: Encoding.Tuple,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Dynamic,
          operator: Operator.EqualTo,
          compValue: first,
        },
        {
          paramType: Encoding.Dynamic,
          operator: Operator.EqualTo,
          compValue: second,
        },
      ],
    })
    expect(conditionId(split("0xaa", "0xbbcc"))).not.toBe(
      conditionId(split("0xaabb", "0xcc"))
    )
  })

  it("tells apart a node's children from its siblings", () => {
    const pass = { paramType: Encoding.Static, operator: Operator.Pass }
    const nested = {
      paramType: Encoding.Tuple,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Tuple,
          operator: Operator.Matches,
          children: [pass],
        },
        pass,
      ],
    }
    const flat = {
      paramType: Encoding.Tuple,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Tuple,
          operator: Operator.Matches,
          children: [pass, pass],
        },
      ],
    }
    expect(conditionId(nested)).not.toBe(conditionId(flat))
  })
})
