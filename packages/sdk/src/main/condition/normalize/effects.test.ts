import { expect, it, suite } from "vitest"

import { Condition, Encoding, Operator } from "../../types"
import { conditionId } from "../conditionId"

import { normalizeCondition } from "."

const word = (n: number) => `0x${n.toString(16).padStart(64, "0")}` as const
const eq = (n: number): Condition => ({
  paramType: Encoding.Static,
  operator: Operator.EqualTo,
  compValue: word(n),
})
const allowance = (key: number): Condition => ({
  paramType: Encoding.Static,
  operator: Operator.WithinAllowance,
  compValue: word(key),
})
const bytesEq = (hex: `0x${string}`): Condition => ({
  paramType: Encoding.Dynamic,
  operator: Operator.EqualTo,
  compValue: hex,
})
const calldata = (...children: Condition[]): Condition => ({
  paramType: Encoding.AbiEncoded,
  operator: Operator.Matches,
  children,
})
const tuple = (...children: Condition[]): Condition => ({
  paramType: Encoding.Tuple,
  operator: Operator.Matches,
  children,
})
const and = (...children: Condition[]): Condition => ({
  paramType: Encoding.None,
  operator: Operator.And,
  children,
})
const or = (...children: Condition[]): Condition => ({
  paramType: Encoding.None,
  operator: Operator.Or,
  children,
})
const pass = (paramType: Encoding, children?: Condition[]): Condition => ({
  paramType,
  operator: Operator.Pass,
  ...(children && { children }),
})
const pluckArray = (slot: number): Condition => ({
  paramType: Encoding.Array,
  operator: Operator.Pluck,
  compValue: `0x${slot.toString(16).padStart(2, "0")}`,
  children: [pass(Encoding.Static)],
})
const zipEvery = (...fields: Condition[]): Condition => ({
  paramType: Encoding.None,
  operator: Operator.ZipEvery,
  compValue: "0x0001",
  children: [tuple(...fields)],
})

suite(
  "normalizeCondition() keeps semantics with effects and id collisions",
  () => {
    it("does not merge Or branches whose packed ids collide", () => {
      // the packed id concatenates headers and compValues without lengths
      const t1 = tuple(bytesEq("0xaa"), bytesEq("0xbb0050cc"))
      const t2 = tuple(bytesEq("0xaa0050bb"), bytesEq("0xcc"))
      expect(conditionId(t1)).toBe(conditionId(t2))

      const result = normalizeCondition(
        or(calldata(t1, eq(1)), calldata(t2, eq(2)))
      )
      // merging would yield calldata(t1, or(eq(1), eq(2))), which also accepts
      // t1 with 2
      expect(result.operator).toBe(Operator.Or)
      expect(result.children).toHaveLength(2)
    })

    it("keeps the order of Or branches that charge allowances", () => {
      // the first passing branch is charged
      const input = calldata(or(allowance(0xbb), allowance(0xaa)))
      expect(normalizeCondition(input)).toEqual(input)
    })

    it("still sorts Or branches without effects", () => {
      expect(normalizeCondition(calldata(or(eq(2), eq(1))))).toEqual(
        calldata(or(eq(1), eq(2)))
      )
    })

    it("keeps duplicate allowance checks in an And (each one charges)", () => {
      const input = calldata(and(allowance(0xaa), allowance(0xaa)))
      expect(normalizeCondition(input)).toEqual(input)
      // duplicates without effects are still removed
      expect(normalizeCondition(calldata(and(eq(1), eq(1))))).toEqual(
        calldata(eq(1))
      )
    })

    it("keeps a Zip after the tuple that plucks its arrays", () => {
      const plucks = tuple(pluckArray(0), pluckArray(1), pass(Encoding.Dynamic))
      const input = calldata(
        and(plucks, zipEvery(pass(Encoding.Static), eq(7)))
      )
      const result = normalizeCondition(input)
      const andNode = result.children![0]
      expect(andNode.operator).toBe(Operator.And)
      expect(andNode.children![0].operator).toBe(Operator.Matches)
      expect(andNode.children![1].operator).toBe(Operator.ZipEvery)
    })

    it("does not push an Or into Ands whose shared children differ in count", () => {
      // Or[And[W, W, A], And[W, B]]: the first branch charges W twice
      const result = normalizeCondition(
        calldata(
          or(
            and(allowance(0xaa), allowance(0xaa), eq(1)),
            and(allowance(0xaa), eq(2))
          )
        )
      )
      expect(result.children![0].operator).toBe(Operator.Or)
    })

    it("still pushes an Or into Ands that share their other children", () => {
      const result = normalizeCondition(
        calldata(or(and(allowance(0xaa), eq(1)), and(allowance(0xaa), eq(2))))
      )
      expect(result).toEqual(calldata(and(allowance(0xaa), or(eq(1), eq(2)))))
    })

    it("does not merge calldata branches with different leading bytes", () => {
      const sel = (s: `0x${string}`, ...children: Condition[]): Condition => ({
        ...calldata(...children),
        compValue: s,
      })
      const input = or(
        sel("0x0004aaaaaaaa", eq(1), eq(2)),
        sel("0x0004bbbbbbbb", eq(1), eq(3))
      )
      // merging would keep only selector aaaaaaaa: sel(a, 1, or(2, 3))
      const result = normalizeCondition(input)
      expect(result.operator).toBe(Operator.Or)
      expect(result.children).toHaveLength(2)
    })

    it("does not merge branches whose differing child charges an allowance", () => {
      // or(m(W, W), m(5, W)): if W(x0) passes but W(x0) + W(x1) exceeds the
      // allowance, the original still tries x0 == 5; the merged form would not
      const result = normalizeCondition(
        or(calldata(allowance(1), allowance(1)), calldata(eq(5), allowance(1)))
      )
      expect(result.operator).toBe(Operator.Or)
    })

    it("keeps the order of an And where a choice depends on earlier charges", () => {
      // And[Or[W(a), W(b)], W(a)]: which Or branch is charged depends on
      // whether W(a) was charged before it
      const choice = or(allowance(0xaa), allowance(0xbb))
      const forward = calldata(and(choice, allowance(0xaa)))
      const backward = calldata(and(allowance(0xaa), choice))
      expect(normalizeCondition(forward)).toEqual(forward)
      expect(normalizeCondition(backward)).toEqual(backward)
    })

    it("pads the parameter a type tree child describes, past non-structural children", () => {
      // f((uint), (uint,uint)) with an ether value check first, and
      // g((uint), (uint,uint,uint)): the type tree lists parameters only
      const ether: Condition = {
        paramType: Encoding.EtherValue,
        operator: Operator.LessThan,
        compValue: word(10),
      }
      const result = normalizeCondition(
        or(
          calldata(ether, tuple(eq(1)), tuple(eq(2), eq(3))),
          calldata(tuple(eq(4)), tuple(eq(5), eq(6), eq(7)))
        )
      )
      const f = result.children!.find(
        (b) => b.children![0].paramType === Encoding.EtherValue
      )!
      // the first tuple keeps its one field, the second gets the third one
      expect(f.children![1].children).toHaveLength(1)
      expect(f.children![2].children).toHaveLength(3)
    })
  }
)
