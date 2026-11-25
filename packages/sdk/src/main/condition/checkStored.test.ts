import { expect, it, suite } from "vitest"

import { Enc, Op, checkStored, tyKey, type FlatNode } from "./checkStored"

/** A tree node; flattened in BFS order like `flattenCondition`. */
type N = { e: number; o: number; cv?: string; ch?: N[] }

const flat = (root: N): FlatNode[] => {
  const out: FlatNode[] = []
  const queue = [{ n: root, parent: 0 }]
  while (queue.length) {
    const { n, parent } = queue.shift()!
    const h = (n.cv ?? "0x").slice(2)
    out.push({
      parent,
      paramType: n.e,
      operator: n.o,
      compValue: Uint8Array.from(h.match(/../g) ?? [], (b) => parseInt(b, 16)),
    })
    const i = out.length - 1
    for (const c of n.ch ?? []) queue.push({ n: c, parent: i })
  }
  return out
}

const word = (n: number) => "0x" + n.toString(16).padStart(64, "0")
const verdict = (root: N, s = true) => {
  const v = checkStored(flat(root), s)
  return v === undefined
    ? "rejected"
    : v.kind === "noCalldata"
      ? "noCalldata"
      : tyKey(v.type)
}

const call = (ch: N[], cv = "0x0004a9059cbb"): N => ({
  e: Enc.AbiEncoded,
  o: Op.Matches,
  cv,
  ch,
})
const eqWord = (n: number): N => ({ e: Enc.Static, o: Op.EqualTo, cv: word(n) })
const pass = (e: number, ch?: N[]): N => ({ e, o: Op.Pass, ch })

suite("checkStored()", () => {
  it("accepts a typed call and returns its type", () => {
    // transfer(address to, uint256 amount) with amount == 1000 (`..`: open,
    // a `Matches` reads the first arguments, there may be more)
    expect(verdict(call([pass(Enc.Static), eqWord(1000)]))).toBe("C4(S,S,..)")
  })

  it("rejects parents and encodings that are not natural numbers", () => {
    const fs = flat(call([pass(Enc.Static), eqWord(1000)]))
    expect(checkStored(fs)).toBeDefined()
    for (const bad of [-1, 0.5]) {
      expect(
        checkStored(fs.map((f, i) => (i === 2 ? { ...f, parent: bad } : f)))
      ).toBeUndefined()
    }
    expect(
      checkStored(fs.map((f, i) => (i === 1 ? { ...f, paramType: 1.5 } : f)))
    ).toBeUndefined()
  })

  it("accepts a root that reads no calldata", () => {
    expect(verdict({ e: Enc.EtherValue, o: Op.LessThan, cv: word(10) })).toBe(
      "noCalldata"
    )
  })

  it("accepts Slice next to a plain check (backlog 4)", () => {
    const slice: N = {
      e: Enc.Static,
      o: Op.Slice,
      cv: "0x001f01",
      ch: [{ e: Enc.Static, o: Op.EqualTo, cv: word(1) }],
    }
    const tree = call([{ e: Enc.None, o: Op.And, ch: [slice, eqWord(1)] }])
    expect(verdict(tree)).toBe("C4(S,..)")
  })

  it("accepts variants only with s = true", () => {
    const a = call([pass(Enc.Static)], "0x000411111111")
    const b = call([pass(Enc.Dynamic)], "0x000422222222")
    const tree = call([{ e: Enc.None, o: Op.Or, ch: [a, b] }])
    // with s = true any bytes value has every call type: the first one
    expect(verdict(tree, true)).toBe("C4(C4(S,..),..)")
    expect(verdict(tree, false)).toBe("rejected")
  })
})
