import { describe, it, expect } from "vitest"
import { Encoding, Condition, Operator } from "../../types"
import { abiEncode } from "../../abiEncode"

import { normalizeCondition } from "."
import { padToMatchTypeTree } from "./padToMatchTypeTree"

// Helper to create test conditions
const COMP = (id: number): Condition => ({
  paramType: Encoding.Static,
  operator: Operator.EqualTo,
  compValue: abiEncode(["uint256"], [id]),
})

const PASS = (paramType: Encoding = Encoding.Static): Condition => ({
  paramType,
  operator: Operator.Pass,
})

const PASS_ = (paramType: Encoding, ...children: Condition[]): Condition => ({
  paramType,
  operator: Operator.Pass,
  children,
})

const OR = (...children: Condition[]): Condition => ({
  paramType: Encoding.None,
  operator: Operator.Or,
  children,
})

const AND = (...children: Condition[]): Condition => ({
  paramType: Encoding.None,
  operator: Operator.And,
  children,
})

const MATCHES = (paramType: Encoding, ...children: Condition[]): Condition => ({
  paramType,
  operator: Operator.Matches,
  children,
})

const DYN = (n: number): Condition => ({
  paramType: Encoding.Dynamic,
  operator: Operator.EqualTo,
  compValue: abiEncode(["bytes"], ["0x" + n.toString(16).padStart(2, "0")]),
})

describe("padToMatchTypeTree", () => {
  describe("Basic padding scenarios", () => {
    it("pads shorter dynamic tuple branch to match longer one", () => {
      const input = OR(
        MATCHES(Encoding.Tuple, DYN(1)), // 1 child
        MATCHES(Encoding.Tuple, DYN(2), COMP(3)) // 2 children
      )

      const result = normalizeCondition(input)

      // Should return OR with both branches having 2 children
      expect(result).toEqual(
        OR(
          MATCHES(Encoding.Tuple, DYN(1), PASS()),
          MATCHES(Encoding.Tuple, DYN(2), COMP(3))
        )
      )
    })

    it("does not pad call variants: the contract accepts them as they are", () => {
      // they may be different calls; padding one with the other's
      // parameters would make it require those
      const input = OR(
        MATCHES(Encoding.AbiEncoded, COMP(1)),
        MATCHES(Encoding.AbiEncoded, COMP(2), COMP(3))
      )

      expect(padToMatchTypeTree(input)).toEqual(input)
      expect(normalizeCondition(input)).toEqual(input)
    })

    it("pads multiple shorter branches to match the longest", () => {
      const input = OR(
        MATCHES(Encoding.Tuple, DYN(4), COMP(5), COMP(6)),
        MATCHES(Encoding.Tuple, DYN(1)),
        MATCHES(Encoding.Tuple, DYN(2), COMP(3))
      )

      const result = normalizeCondition(input)

      expect(result).toEqual(
        OR(
          MATCHES(Encoding.Tuple, DYN(1), PASS(), PASS()),
          MATCHES(Encoding.Tuple, DYN(2), COMP(3), PASS()),
          MATCHES(Encoding.Tuple, DYN(4), COMP(5), COMP(6))
        )
      )
    })

    it("does not pad when all branches have same length", () => {
      const input = OR(
        MATCHES(Encoding.AbiEncoded, COMP(1), COMP(2)),
        MATCHES(Encoding.AbiEncoded, COMP(3), COMP(4))
      )

      const expected = OR(
        MATCHES(Encoding.AbiEncoded, COMP(1), COMP(2)),
        MATCHES(Encoding.AbiEncoded, COMP(3), COMP(4))
      )

      expect(padToMatchTypeTree(input)).toEqual(expected)
      expect(normalizeCondition(input)).toEqual(expected)
    })

    it("preserves Dynamic nodes when copying structure", () => {
      const dynamic = {
        paramType: Encoding.Dynamic,
        operator: Operator.EqualTo,
        compValue: abiEncode(["string"], ["Hello World"]),
      }

      const input = OR(
        MATCHES(Encoding.Tuple, DYN(1)),
        MATCHES(Encoding.Tuple, DYN(2), dynamic)
      )

      const expected = OR(
        MATCHES(Encoding.Tuple, DYN(1), PASS(Encoding.Dynamic)),
        MATCHES(Encoding.Tuple, DYN(2), dynamic)
      )

      expect(padToMatchTypeTree(input)).toEqual(expected)
      expect(normalizeCondition(input)).toEqual(expected)
    })
  })

  describe("parameters types", () => {
    it("pads AbiEncoded fields of a tuple", () => {
      const input = OR(
        MATCHES(Encoding.Tuple, MATCHES(Encoding.AbiEncoded, COMP(1))),
        MATCHES(
          Encoding.Tuple,
          MATCHES(Encoding.AbiEncoded, COMP(2), COMP(3), COMP(4))
        )
      )

      const result = normalizeCondition(input)

      expect(padToMatchTypeTree(input)).toEqual(
        OR(
          MATCHES(
            Encoding.Tuple,
            MATCHES(Encoding.AbiEncoded, COMP(1), PASS(), PASS())
          ),
          MATCHES(
            Encoding.Tuple,
            MATCHES(Encoding.AbiEncoded, COMP(2), COMP(3), COMP(4))
          )
        )
      )
      // the Or is then pushed down to the calldata, where it needs no padding
      expect(result).toEqual(
        MATCHES(
          Encoding.Tuple,
          OR(
            MATCHES(Encoding.AbiEncoded, COMP(1)),
            MATCHES(Encoding.AbiEncoded, COMP(2), COMP(3), COMP(4))
          )
        )
      )
    })

    it("does not pad static tuples: they would grow and move what follows", () => {
      const input = OR(
        MATCHES(Encoding.Tuple, COMP(1), COMP(2)),
        MATCHES(Encoding.Tuple, COMP(3))
      )

      expect(padToMatchTypeTree(input)).toEqual(input)
    })

    it("handles mixed types, pads matching types", () => {
      const dynamic: Condition = {
        operator: Operator.EqualTo,
        paramType: Encoding.Dynamic,
        compValue: "0xaabbccdd",
      }

      const input = OR(
        MATCHES(Encoding.Tuple, DYN(1)),
        dynamic,
        MATCHES(Encoding.Tuple, DYN(4), COMP(5))
      )

      const expected = OR(
        MATCHES(Encoding.Tuple, DYN(1), PASS()),
        dynamic,
        MATCHES(Encoding.Tuple, DYN(4), COMP(5))
      )

      expect(padToMatchTypeTree(input)).toEqual(expected)
    })
  })

  describe("Nested structures", () => {
    it("finds complex branches inside nested logical operators", () => {
      const input = AND(
        OR(MATCHES(Encoding.Tuple, DYN(1)), MATCHES(Encoding.Tuple, DYN(3), COMP(4))),
        OR(
          MATCHES(Encoding.Tuple, DYN(8)),
          MATCHES(Encoding.Tuple, DYN(5), COMP(6), COMP(7))
        )
      )

      const expected = AND(
        OR(
          MATCHES(Encoding.Tuple, DYN(1), PASS(), PASS()),
          MATCHES(Encoding.Tuple, DYN(3), COMP(4), PASS())
        ),
        OR(
          MATCHES(Encoding.Tuple, DYN(8), PASS(), PASS()),
          MATCHES(Encoding.Tuple, DYN(5), COMP(6), COMP(7))
        )
      )

      expect(normalizeCondition(input)).toEqual(expected)
    })

    it("handles complex branches inside Arrays", () => {
      const input = OR(
        MATCHES(Encoding.Array, MATCHES(Encoding.AbiEncoded, COMP(1)), PASS()),
        MATCHES(Encoding.Array, MATCHES(Encoding.AbiEncoded, COMP(2), COMP(3)))
      )

      const expected = OR(
        MATCHES(
          Encoding.Array,
          MATCHES(Encoding.AbiEncoded, COMP(1), PASS()),
          PASS()
        ),
        MATCHES(Encoding.Array, MATCHES(Encoding.AbiEncoded, COMP(2), COMP(3)))
      )

      expect(padToMatchTypeTree(input)).toEqual(expected)
      expect(normalizeCondition(input)).toEqual(expected)
    })

    it("two branches which should mutually pad eachother", () => {
      const input = OR(
        MATCHES(Encoding.Tuple, MATCHES(Encoding.Tuple, DYN(1), COMP(1))),
        MATCHES(
          Encoding.Tuple,
          MATCHES(Encoding.Tuple, DYN(2)),
          MATCHES(
            Encoding.Tuple,
            COMP(2),
            COMP(3),
            MATCHES(Encoding.Array, COMP(3))
          )
        )
      )

      const expected = OR(
        MATCHES(
          Encoding.Tuple,
          MATCHES(Encoding.Tuple, DYN(1), COMP(1)),
          PASS_(Encoding.Tuple, PASS(), PASS(), PASS_(Encoding.Array, PASS()))
        ),
        MATCHES(
          Encoding.Tuple,
          MATCHES(Encoding.Tuple, DYN(2), PASS()),
          MATCHES(
            Encoding.Tuple,
            COMP(2),
            COMP(3),
            MATCHES(Encoding.Array, COMP(3))
          )
        )
      )

      expect(padToMatchTypeTree(input)).toEqual(expected)
    })

    it("copies complex structure when padding", () => {
      const input = OR(
        MATCHES(Encoding.Tuple, DYN(2)),
        MATCHES(
          Encoding.Tuple,
          DYN(1),
          MATCHES(
            Encoding.Tuple,
            COMP(2),
            COMP(3),
            MATCHES(Encoding.Array, COMP(4))
          )
        )
      )

      const insertedSubTree = {
        operator: Operator.Pass,
        paramType: Encoding.Tuple,
        children: [
          PASS(),
          PASS(),
          {
            operator: Operator.Pass,
            paramType: Encoding.Array,
            children: [PASS()],
          },
        ],
      }

      const expected = OR(
        MATCHES(Encoding.Tuple, DYN(2), insertedSubTree),
        MATCHES(
          Encoding.Tuple,
          DYN(1),
          MATCHES(
            Encoding.Tuple,
            COMP(2),
            COMP(3),
            MATCHES(Encoding.Array, COMP(4))
          )
        )
      )

      expect(padToMatchTypeTree(input)).toEqual(expected)
    })

    it("handles complex branches inside Arrays", () => {
      // the element type of two checks of one array must agree, so the
      // calldata elements are padded (unlike call variants of one value)
      const input = OR(
        MATCHES(Encoding.Array, MATCHES(Encoding.AbiEncoded, COMP(1)), PASS()),
        MATCHES(Encoding.Array, MATCHES(Encoding.AbiEncoded, COMP(2), COMP(3)))
      )

      const expected = OR(
        MATCHES(
          Encoding.Array,
          MATCHES(Encoding.AbiEncoded, COMP(1), PASS()),
          PASS()
        ),
        MATCHES(Encoding.Array, MATCHES(Encoding.AbiEncoded, COMP(2), COMP(3)))
      )

      expect(padToMatchTypeTree(input)).toEqual(expected)
      expect(normalizeCondition(input)).toEqual(expected)
    })
  })

  describe("Arrays", () => {
    it("pads dynamic tuple elements", () => {
      const input = MATCHES(
        Encoding.Array,
        MATCHES(Encoding.Tuple, DYN(1), PASS(), COMP(3)),
        MATCHES(Encoding.Tuple, DYN(4))
      )

      const expected = MATCHES(
        Encoding.Array,
        MATCHES(Encoding.Tuple, DYN(1), PASS(), COMP(3)),
        MATCHES(Encoding.Tuple, DYN(4), PASS(), PASS())
      )

      expect(padToMatchTypeTree(input)).toEqual(expected)
      expect(normalizeCondition(input)).toEqual(expected)
    })

    it("does not pad static tuple elements", () => {
      const input = MATCHES(
        Encoding.Array,
        MATCHES(Encoding.Tuple, COMP(1), PASS(), COMP(3)),
        MATCHES(Encoding.Tuple, COMP(4))
      )

      expect(padToMatchTypeTree(input)).toEqual(input)
    })
  })

  describe("Nothing to handle", () => {
    it("handles condition with no complex branches", () => {
      const input = OR(COMP(1), COMP(2), COMP(3))

      expect(padToMatchTypeTree(input)).toEqual(input)
      expect(normalizeCondition(input)).toEqual(input)
    })
  })
})
