import { describe, expect, it } from "vitest"
import { Operator, Encoding } from "../../../types"

import { abiEncodedMatches, calldataMatches } from "./matches"
import { encodeKey } from "../../../keys"
import { AbiCoder, ParamType } from "ethers"
import { checkRootConditionIntegrity } from "../../../condition/conditionIntegrity"

describe("calldataMatches", () => {
  it("correctly encodes CallWithinAllowance conditions", () => {
    const result = calldataMatches([], [], {
      callWithinAllowance: encodeKey("test-allowance"),
    })()

    // no parameters: the allowance alone (a root that reads no calldata)
    expect(result).toEqual({
      paramType: Encoding.None,
      operator: Operator.CallWithinAllowance,
      compValue: encodeKey("test-allowance"),
    })
    expect(() => checkRootConditionIntegrity(result)).not.toThrow()
    expect(() => checkRootConditionIntegrity(result)).not.toThrow()
  })

  it("scopes a bytes parameter with a nested allowance-only call", () => {
    const inner = calldataMatches([], [], { callWithinAllowance: "test" })
    const result = calldataMatches([inner], ["bytes"])()
    expect(result.children![0]).toEqual({
      paramType: Encoding.None,
      operator: Operator.And,
      children: [
        { paramType: Encoding.Dynamic, operator: Operator.Pass },
        {
          paramType: Encoding.None,
          operator: Operator.CallWithinAllowance,
          compValue: encodeKey("test"),
        },
      ],
    })
    expect(() => checkRootConditionIntegrity(result)).not.toThrow()
    expect(() => checkRootConditionIntegrity(result)).not.toThrow()
  })

  it("puts CallWithinAllowance next to the Matches, as v3 requires", () => {
    const result = calldataMatches([1], ["uint256"], {
      callWithinAllowance: "test-allowance",
    })()

    expect(result).toEqual({
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
              compValue: AbiCoder.defaultAbiCoder().encode(["uint256"], [1]),
            },
          ],
        },
        {
          paramType: Encoding.None,
          operator: Operator.CallWithinAllowance,
          compValue: encodeKey("test-allowance"),
        },
      ],
    })
    expect(() => checkRootConditionIntegrity(result)).not.toThrow()
  })

  it("adds the selector check next to the allowance", () => {
    const result = calldataMatches([1], ["uint256"], {
      selector: "0x12345678",
      callWithinAllowance: "test-allowance",
    })()
    expect(result.operator).toBe(Operator.And)
    expect(result.children!.map((c) => c.operator)).toEqual([
      Operator.Matches,
      Operator.CallWithinAllowance,
      Operator.Bitmask,
    ])
  })

  it("accepts allowance keys as labels", () => {
    expect(
      calldataMatches([], [], {
        callWithinAllowance: "test-allowance",
      })()
    ).toEqual(
      calldataMatches([], [], {
        callWithinAllowance: encodeKey("test-allowance"),
      })()
    )
  })

  it("encodes an allowance key that is not already bytes32", () => {
    // This path assigns `compValue` directly, so before it went through
    // `encodeKey` a short hex reached the chain as a 2-byte compValue.
    expect(
      calldataMatches([], [], { callWithinAllowance: "0x1234" })()
    ).toEqual(
      calldataMatches([], [], {
        callWithinAllowance: encodeKey("0x1234"),
      })()
    )
  })
})

describe("calldataMatches scopings", () => {
  it("throws on more scopings than parameters", () => {
    expect(() => calldataMatches([1, 2], ["uint256"])()).toThrow(
      "2 scopings for 1 parameters"
    )
    expect(() => abiEncodedMatches([1, 2], ["uint256"])()).toThrow(
      "2 scopings for 1 parameters"
    )
  })

  it("throws on scopings that are not an array", () => {
    expect(() => calldataMatches({ a: 1 } as any, ["uint256 a"])()).toThrow(
      "array of scopings"
    )
  })

  it("throws on a null scoping", () => {
    expect(() => calldataMatches([null as any], ["uint256"])()).toThrow(
      "must not be null"
    )
  })

  it("throws at the top level when there is nothing to check", () => {
    expect(() => calldataMatches([], [])()).toThrow("checks nothing")
  })

  it("checks only the selector of a call without parameters on bytes", () => {
    const result = calldataMatches([], [], { selector: "0x12345678" })(
      ParamType.from("bytes")
    )
    expect(result).toEqual({
      paramType: Encoding.None,
      operator: Operator.And,
      children: [
        { paramType: Encoding.Dynamic, operator: Operator.Pass },
        {
          paramType: Encoding.Dynamic,
          operator: Operator.Bitmask,
          compValue: "0x0000ffffffff12345678",
        },
      ],
    })
  })

  it("checks a function permission's selector with a 4-byte mask", () => {
    const result = calldataMatches({
      targetAddress: "0x0000000000000000000000000000000000000001",
      selector: "0x12345678",
    })(ParamType.from("bytes"))
    expect(result).toEqual({
      paramType: Encoding.Dynamic,
      operator: Operator.Bitmask,
      compValue: "0x0000ffffffff12345678",
    })
  })
})
