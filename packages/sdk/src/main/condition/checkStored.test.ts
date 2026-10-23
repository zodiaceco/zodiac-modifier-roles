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
const pluck = (e: number, slot: number, ch?: N[]): N => ({
  e,
  o: Op.Pluck,
  cv: "0x" + slot.toString(16).padStart(2, "0"),
  ch,
})
const zip = (slots: number[], fields: N[]): N => ({
  e: Enc.None,
  o: Op.ZipEvery,
  cv: "0x" + slots.map((s) => s.toString(16).padStart(2, "0")).join(""),
  ch: [{ e: Enc.Tuple, o: Op.Matches, ch: fields }],
})

suite("checkStored()", () => {
  it("accepts a typed call and returns its type", () => {
    // transfer(address to, uint256 amount) with amount == 1000
    expect(verdict(call([pass(Enc.Static), eqWord(1000)]))).toBe("C4(S,S)")
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

  it("accepts Zips at the root and rejects them among parameters (backlog 1)", () => {
    const arr = () => [pass(Enc.Static)]
    const plucks = [pluck(Enc.Array, 0, arr()), pluck(Enc.Array, 1, arr())]
    const fields = [eqWord(5), pass(Enc.Static)]
    const ok: N = {
      e: Enc.None,
      o: Op.And,
      ch: [call(plucks), zip([0, 1], fields)],
    }
    expect(verdict(ok)).toBe("C4(A(S),A(S))")

    const bypass = call([
      pluck(Enc.Array, 0, arr()),
      pluck(Enc.Array, 1, arr()),
      zip([0, 1], [eqWord(5), pass(Enc.Static)]),
      eqWord(5),
    ])
    expect(verdict(bypass)).toBe("rejected")
  })

  it("rejects a Zip that reads a slot no Pluck writes first", () => {
    const arr = () => [pass(Enc.Static)]
    const unwritten: N = {
      e: Enc.None,
      o: Op.And,
      ch: [
        zip([0, 1], [eqWord(5), pass(Enc.Static)]),
        call([pluck(Enc.Array, 0, arr()), pluck(Enc.Array, 1, arr())]),
      ],
    }
    expect(verdict(unwritten)).toBe("rejected")
    // a Pluck in only one branch of an Or does not count
    const orBranch: N = {
      e: Enc.None,
      o: Op.And,
      ch: [
        {
          e: Enc.None,
          o: Op.Or,
          ch: [
            call([pluck(Enc.Array, 0, arr()), pluck(Enc.Array, 1, arr())]),
            call([pass(Enc.Array, arr()), pass(Enc.Array, arr())]),
          ],
        },
        zip([0, 1], [eqWord(5), pass(Enc.Static)]),
      ],
    }
    expect(verdict(orBranch)).toBe("rejected")
  })

  it("rejects a non-structural child in a Pass tuple (backlog 2)", () => {
    const tree = call([
      pass(Enc.Tuple, [
        pass(Enc.Static),
        { e: Enc.EtherValue, o: Op.LessThan, cv: word(1) },
      ]),
    ])
    expect(verdict(tree)).toBe("rejected")
  })

  it("accepts Slice next to a plain check, which Integrity rejects (backlog 4)", () => {
    const slice: N = {
      e: Enc.Static,
      o: Op.Slice,
      cv: "0x001f01",
      ch: [{ e: Enc.Static, o: Op.EqualTo, cv: word(1) }],
    }
    const tree = call([{ e: Enc.None, o: Op.And, ch: [slice, eqWord(1)] }])
    expect(verdict(tree)).toBe("C4(S)")
  })

  it("accepts variants only with s = true", () => {
    const a = call([pass(Enc.Static)], "0x000411111111")
    const b = call([pass(Enc.Dynamic)], "0x000422222222")
    const tree = call([{ e: Enc.None, o: Op.Or, ch: [a, b] }])
    expect(verdict(tree, true)).toBe("C4(D)")
    expect(verdict(tree, false)).toBe("rejected")
  })

  it("rejects what the packer cannot encode or Integrity's operator rules forbid", () => {
    // Pluck index 255 overflows the header's maxPluck byte
    expect(verdict(call([pluck(Enc.Static, 255)]))).toBe("rejected")
    // GreaterThan needs a 32-byte compValue
    expect(
      verdict(call([{ e: Enc.Static, o: Op.GreaterThan, cv: "0x01" }]))
    ).toBe("rejected")
    // placeholder operator code
    expect(verdict(call([{ e: Enc.Static, o: 3 }]))).toBe("rejected")
    // not in BFS order
    const fs = flat(call([pass(Enc.Static), pass(Enc.Static)]))
    fs[2].parent = 5
    expect(checkStored(fs)).toBeUndefined()
  })
})
