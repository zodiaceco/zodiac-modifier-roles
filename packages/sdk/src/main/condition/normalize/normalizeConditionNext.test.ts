import { describe, it, expect } from "vitest"
import { Encoding, Operator, Condition } from "../../types"
import { normalizeCondition } from "."
import { abiEncode } from "../../abiEncode"
import { conditionHash, conditionId } from "../conditionId"

// Helper to create a static comparison condition
const COMP = (id: number | `0x${string}`): Condition => ({
  paramType: Encoding.Static,
  operator: Operator.EqualTo,
  compValue: typeof id === "string" ? id : abiEncode(["uint256"], [id]),
})

// Helper to create a PASS condition
const PASS = (paramType: Encoding = Encoding.Static): Condition => ({
  paramType,
  operator: Operator.Pass,
})

// Helper to create dynamic conditions
const DYNAMIC = (operator: Operator = Operator.Pass): Condition => ({
  paramType: Encoding.Dynamic,
  operator,
})

// Helper to create a MATCHES condition
const MATCHES = (paramType: Encoding, ...children: Condition[]): Condition => ({
  paramType,
  operator: Operator.Matches,
  children,
})

// Helper to create logical conditions
const AND = (...children: Condition[]): Condition => ({
  paramType: Encoding.None,
  operator: Operator.And,
  children,
})

const OR = (...children: Condition[]): Condition => ({
  paramType: Encoding.None,
  operator: Operator.Or,
  children,
})

const CALL_ALLOWANCE = (): Condition => ({
  paramType: Encoding.None,
  operator: Operator.CallWithinAllowance,
})

describe("normalizeCondition", () => {
  describe("Core normalization steps", () => {
    describe("pruneTrailingPass", () => {
      it("prunes trailing Pass nodes from AbiEncoded MATCHES", () => {
        const input = MATCHES(Encoding.AbiEncoded, COMP(1), PASS(), PASS())

        const result = normalizeCondition(input)

        expect(result).toEqual({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [COMP(1)],
        })
      })

      it("prunes trailing Pass nodes from dynamic tuples", () => {
        const input = MATCHES(
          Encoding.Tuple,
          DYNAMIC(Operator.EqualToAvatar),
          PASS(),
          PASS()
        )

        const result = normalizeCondition(input)

        expect(result).toEqual({
          paramType: Encoding.Tuple,
          operator: Operator.Matches,
          children: [DYNAMIC(Operator.EqualToAvatar)],
        })
      })

      it("does NOT prune trailing Pass nodes from static tuples", () => {
        const input = MATCHES(Encoding.Tuple, COMP(1), PASS(), PASS())

        const result = normalizeCondition(input)

        expect(result).toEqual({
          paramType: Encoding.Tuple,
          operator: Operator.Matches,
          children: [COMP(1), PASS(), PASS()],
        })
      })

      it("keeps allowance conditions while pruning Pass nodes", () => {
        const input = MATCHES(
          Encoding.AbiEncoded,
          CALL_ALLOWANCE(),
          PASS(),
          PASS()
        )

        const result = normalizeCondition(input)

        expect(result).toEqual({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [PASS(), CALL_ALLOWANCE()],
        })
      })

      it("preserves first child even if it's Pass", () => {
        const input = MATCHES(Encoding.AbiEncoded, PASS(), PASS(), PASS())

        const result = normalizeCondition(input)

        expect(result).toEqual({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [PASS()],
        })
      })
    })

    describe("flattenNestedLogicalConditions", () => {
      it("flattens nested AND conditions", () => {
        const input = AND(COMP(1), AND(COMP(2), COMP(3)), COMP(4))

        const result = normalizeCondition(input)

        expect(result).toEqual({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [COMP(1), COMP(2), COMP(3), COMP(4)],
        })
      })

      it("flattens nested OR conditions", () => {
        const input = OR(COMP(1), OR(COMP(2), COMP(3)), COMP(4))

        const result = normalizeCondition(input)

        expect(result).toEqual({
          paramType: Encoding.None,
          operator: Operator.Or,
          children: [COMP(1), COMP(2), COMP(3), COMP(4)],
        })
      })

      it("does NOT flatten different logical operators", () => {
        const input = AND(COMP(1), OR(COMP(2), COMP(3)), COMP(4))

        const result = normalizeCondition(input)

        expect(result).toEqual({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            COMP(1),
            COMP(4),
            {
              paramType: Encoding.None,
              operator: Operator.Or,
              children: [COMP(2), COMP(3)],
            },
          ],
        })
      })
    })

    describe("dedupeBranches", () => {
      it("removes duplicate children in AND conditions", () => {
        const input = AND(COMP(1), COMP(2), COMP(1), COMP(3))

        const result = normalizeCondition(input)

        expect(result).toEqual({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [COMP(1), COMP(2), COMP(3)],
        })
      })

      it("removes duplicate children in OR conditions", () => {
        const input = OR(COMP(1), COMP(2), COMP(1), COMP(3))

        const result = normalizeCondition(input)

        expect(result).toEqual({
          paramType: Encoding.None,
          operator: Operator.Or,
          children: [COMP(1), COMP(2), COMP(3)],
        })
      })

      it("handles complex nested duplicates", () => {
        const branch1 = AND(COMP(1), COMP(2))
        const branch2 = AND(COMP(1), COMP(2)) // Semantically identical
        const input = OR(branch1, COMP(3), branch2)

        const result = normalizeCondition(input)

        const normalized = result
        expect(normalized.children).toHaveLength(2)

        expect(result).toEqual(OR(COMP(3), branch1))
      })
    })

    describe("unwrapSingleBranches", () => {
      it("unwraps AND with single child", () => {
        const input = AND(COMP(1))

        const result = normalizeCondition(input)

        expect(result).toEqual(COMP(1))
      })

      it("unwraps OR with single child", () => {
        const input = OR(COMP(1))

        const result = normalizeCondition(input)

        expect(result).toEqual(COMP(1))
      })

      it("handles unwrapping after deduplication", () => {
        const input = AND(COMP(1), COMP(1)) // Duplicates will be removed, leaving single child

        const result = normalizeCondition(input)

        expect(result).toEqual(COMP(1))
      })
    })

    describe("sortChildren", () => {
      it("sorts children by their condition IDs in AND", () => {
        const input = AND(COMP(3), COMP(1), COMP(2))

        const result = normalizeCondition(input)

        expect(result).toEqual(AND(COMP(1), COMP(2), COMP(3)))
      })

      it("moves AbiEncoded children to front regardless of ID order", () => {
        const abiEncodedChild1 = MATCHES(Encoding.AbiEncoded, COMP(1))
        const staticChild = COMP(2)
        const abiEncodedChild2 = MATCHES(Encoding.AbiEncoded, COMP(3))

        const input = OR(staticChild, abiEncodedChild1, abiEncodedChild2)

        const result = normalizeCondition(input)
        expect(result).toEqual(
          OR(abiEncodedChild1, abiEncodedChild2, staticChild)
        )
      })
    })

    describe("deleteUndefinedFields", () => {
      it("removes undefined children field", () => {
        const condition: Condition = {
          paramType: Encoding.Static,
          operator: Operator.Pass,
          children: undefined,
        }

        const result = normalizeCondition(condition)

        expect(result).not.toHaveProperty("children")
      })

      it("removes undefined compValue field", () => {
        const condition: Condition = {
          paramType: Encoding.Static,
          operator: Operator.Pass,
          compValue: undefined,
        }

        const result = normalizeCondition(condition)

        expect(result).not.toHaveProperty("compValue")
      })

      it("preserves defined fields", () => {
        const condition: Condition = {
          paramType: Encoding.Static,
          operator: Operator.EqualTo,
          compValue: "0x01",
          children: [COMP(1)],
        }

        const result = normalizeCondition(condition)

        const normalized = result
        expect(normalized).toHaveProperty("compValue", "0x01")
        expect(normalized).toHaveProperty("children")
      })
    })
  })

  describe("Misc", () => {
    it("combines multiple normalization steps correctly", () => {
      // Complex condition that exercises multiple normalization steps
      const input = OR(
        AND(COMP(1), COMP(1)), // Duplicate -> single child -> unwrap
        AND(COMP(2), COMP(3)), // Normal case
        MATCHES(Encoding.AbiEncoded, COMP(4), PASS(), PASS()) // Prune trailing Pass
      )

      const result = normalizeCondition(input)

      expect(result).toEqual(
        OR(
          MATCHES(Encoding.AbiEncoded, COMP(4)),
          COMP(1),
          AND(COMP(2), COMP(3))
        )
      )
    })

    it("handles deep nesting with multiple normalization steps", () => {
      const input = AND(
        OR(AND(COMP(1), COMP(1)), COMP(2)), // Nested logic with dedup/unwrap
        MATCHES(Encoding.AbiEncoded, COMP(3), PASS()) // Prune Pass
      )

      const result = normalizeCondition(input)

      expect(result).toEqual(
        AND(MATCHES(Encoding.AbiEncoded, COMP(3)), OR(COMP(1), COMP(2)))
      )
    })

    it("preserves semantics through complex transformations", () => {
      // static tuples of different lengths are different types: padding
      // would change what the shorter one reads
      const input = OR(
        MATCHES(Encoding.Tuple, COMP(1)),
        MATCHES(Encoding.Tuple, COMP(2), COMP(3), COMP(4))
      )

      expect(normalizeCondition(input)).toEqual(input)
    })
    it("push down + pad", () => {
      // inside a parameter (not a call variant), the shorter branch is padded
      // and the Or pushed down to the field that differs
      const DYN: Condition = {
        paramType: Encoding.Dynamic,
        operator: Operator.EqualTo,
        compValue: "0x12",
      }
      const input = OR(
        MATCHES(Encoding.Tuple, DYN, COMP(2)),
        MATCHES(Encoding.Tuple, DYN)
      )

      const result = normalizeCondition(input)

      expect(result).toEqual(MATCHES(Encoding.Tuple, DYN, OR(PASS(), COMP(2))))
    })
  })

  describe("Edge cases", () => {
    it("handles conditions without children", () => {
      const input = COMP(1)

      const result = normalizeCondition(input)

      expect(result).toEqual(COMP(1))
    })

    it("handles conditions with allowance operators", () => {
      const input = MATCHES(Encoding.AbiEncoded, CALL_ALLOWANCE(), PASS())

      const result = normalizeCondition(input)

      expect(result).toEqual({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [PASS(), CALL_ALLOWANCE()],
      })
    })

    it("handles differences in children and compValue", () => {
      const input1: Condition = {
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        compValue: "0x",
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.EqualTo,
            compValue: abiEncode(["uint256"], [1]),
            children: [],
          },
        ],
      }

      const input2: Condition = {
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        compValue: "0x",
        children: [
          {
            compValue: abiEncode(["uint256"], [1]),
            operator: Operator.EqualTo,
            paramType: Encoding.Static,
            children: null as any,
          },
        ],
      }

      expect(conditionId(normalizeCondition(input1))).toEqual(
        conditionId(normalizeCondition(input2))
      )
    })
  })

  describe("ID management", () => {
    it("produces stable IDs for semantically identical conditions", () => {
      const condition1 = AND(COMP(1), COMP(2))
      const condition2 = AND(COMP(2), COMP(1)) // Different order

      const result1 = normalizeCondition(condition1)
      const result2 = normalizeCondition(condition2)

      expect(conditionId(result1)).toBe(conditionId(result2))
      expect(conditionHash(result1)).toBe(conditionHash(result2))
    })

    it("produces stable IDs for deduping, even on different key ordering", () => {
      const c1: Condition = {
        paramType: Encoding.Static,
        operator: Operator.EqualTo,
        compValue: "0x",
      }

      const c2: Condition = {
        operator: Operator.EqualTo,
        paramType: Encoding.Static,
        compValue: "0x",
      }

      const result = normalizeCondition(AND(c1, c2))

      expect(result).toEqual(c1)
    })

    it("produces stable IDs for deduping, even on mismatched, but equivalent, fields", () => {
      const c1: Condition = {
        paramType: Encoding.Static,
        operator: Operator.EqualTo,
        compValue: "0x",
      }

      const c2: Condition = {
        operator: Operator.EqualTo,
        paramType: Encoding.Static,
        children: [],
      }

      const result = normalizeCondition(AND(c1, c2))

      expect(result).toEqual(c1)
    })
  })

  describe("Regression and idempotency", () => {
    it("is idempotent - normalize(normalize(x)) === normalize(x)", () => {
      const input = OR(
        AND(COMP(1), COMP(1)),
        MATCHES(Encoding.AbiEncoded, COMP(2), PASS()),
        COMP(3)
      )

      const result1 = normalizeCondition(input)
      const result2 = normalizeCondition(result1)

      expect(conditionHash(result1)).toEqual(conditionHash(result2))
    })

    it("produces consistent results across multiple calls", () => {
      const input = AND(
        OR(COMP(1), COMP(2)),
        MATCHES(Encoding.AbiEncoded, COMP(3), PASS(), PASS())
      )

      const results = Array.from({ length: 5 }, () => normalizeCondition(input))

      const firstId = conditionId(results[0])
      results.forEach((result) => {
        expect(conditionId(result)).toBe(firstId)
      })
    })

    it("handles performance with large condition trees", () => {
      // Create a large OR condition with many branches
      const largeBranches = Array.from({ length: 100 }, (_, i) => COMP(i))
      const largeCondition = OR(...largeBranches)

      const start = performance.now()
      normalizeCondition(largeCondition)
      const end = performance.now()

      expect(end - start).toBeLessThan(50) // Should complete in under 50 ms
    })
  })
})
