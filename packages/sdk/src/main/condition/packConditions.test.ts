import { expect, it, suite } from "vitest"

import { Enc, Op } from "./checkStored"
import { checkAndPack, packConditions } from "./packConditions"

const word = (n: number) => "0x" + n.toString(16).padStart(64, "0")

suite("packConditions()", () => {
  it("packs transfer(address, uint256 == 1000)", () => {
    // AbiEncoded:Matches (no leading bytes given) [Static:Pass, Static:EqualTo(1000)]
    const flat = [
      {
        parent: 0,
        paramType: Enc.AbiEncoded,
        operator: Op.Matches,
        compValue: "0x",
      },
      { parent: 0, paramType: Enc.Static, operator: Op.Pass, compValue: "0x" },
      {
        parent: 0,
        paramType: Enc.Static,
        operator: Op.EqualTo,
        compValue: word(1000),
      },
    ]
    const { verdict, packed } = checkAndPack(flat)
    expect(verdict).toEqual({
      kind: "typed",
      type: { k: "call", lb: 4, ts: [{ k: "static" }, { k: "static" }] },
    })
    expect(packed).toBe(
      "0x" +
        "000300" + // 3 nodes, no Pluck
        "a5008001" + // AbiEncoded, Matches, 2 children, not inlined, has compValue
        "20000040" + // Static, Pass, inlined size 32
        "30000041" + // Static, EqualTo, inlined size 32, has compValue
        "0002" +
        "0004" + // default leading bytes (selector)
        "0020" +
        word(1000).slice(2)
    )
  })

  it("drops the offset word of a non-inlined EqualTo compValue", () => {
    // f(bytes) == "hi": compValue is abi.encode(bytes("hi"))
    const encoded =
      word(32).slice(2) + word(2).slice(2) + "6869".padEnd(64, "0")
    const flat = [
      {
        parent: 0,
        paramType: Enc.AbiEncoded,
        operator: Op.Matches,
        compValue: "0x0004",
      },
      {
        parent: 0,
        paramType: Enc.Dynamic,
        operator: Op.EqualTo,
        compValue: "0x" + encoded,
      },
    ]
    const { packed } = checkAndPack(flat)
    expect(packed.endsWith("0040" + encoded.slice(64))).toBe(true)
  })

  it("refuses arrays the packer cannot encode", () => {
    const notBfs = [
      {
        parent: 0,
        paramType: Enc.AbiEncoded,
        operator: Op.Matches,
        compValue: new Uint8Array(0),
      },
      {
        parent: 2,
        paramType: Enc.Static,
        operator: Op.Pass,
        compValue: new Uint8Array(0),
      },
      {
        parent: 0,
        paramType: Enc.Static,
        operator: Op.Pass,
        compValue: new Uint8Array(0),
      },
    ]
    expect(() => packConditions(notBfs)).toThrow("not packable")
  })

  it("refuses arrays checkStored rejects", () => {
    const flat = [
      {
        parent: 0,
        paramType: Enc.AbiEncoded,
        operator: Op.Matches,
        compValue: "0x0004",
      },
      {
        parent: 0,
        paramType: Enc.Static,
        operator: Op.GreaterThan,
        compValue: "0x01",
      },
    ]
    expect(() => checkAndPack(flat)).toThrow("rejected")
  })
})
