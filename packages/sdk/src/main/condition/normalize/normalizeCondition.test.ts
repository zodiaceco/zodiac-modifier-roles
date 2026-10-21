import { expect, it, suite } from "vitest"
import { Encoding, Condition, Operator } from "../../types"

import { normalizeCondition } from "."

import { FunctionPermissionCoerced, mergePermissions } from "../../permission"
import { abiEncode } from "../../abiEncode"

import { c } from "../../target/authoring"
import { allow } from "../../../kit"
import { encodeKey } from "../../keys"

const DUMMY_COMP = (id: number) => ({
  paramType: Encoding.Static,
  operator: Operator.EqualTo, // side-effect free (a Custom adapter may charge allowances)
  compValue: abiEncode(["uint256"], [id]),
})

suite("normalizeCondition()", () => {
  it("flattens nested AND conditions", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.None,
        operator: Operator.And,

        children: [
          {
            paramType: Encoding.None,
            operator: Operator.And,
            children: [
              DUMMY_COMP(0),
              {
                paramType: Encoding.None,
                operator: Operator.And,
                children: [DUMMY_COMP(1), DUMMY_COMP(2)],
              },
            ],
          },
          DUMMY_COMP(3),
        ],
      })
    ).to.deep.equal({
      paramType: Encoding.None,
      operator: Operator.And,
      children: [DUMMY_COMP(0), DUMMY_COMP(1), DUMMY_COMP(2), DUMMY_COMP(3)],
    })
  })

  it("does not flatten ORs in ANDs", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [
          {
            paramType: Encoding.None,
            operator: Operator.Or,
            children: [DUMMY_COMP(0), DUMMY_COMP(1)],
          },
          DUMMY_COMP(3),
        ],
      })
    ).to.deep.equal({
      paramType: Encoding.None,
      operator: Operator.And,
      children: [
        DUMMY_COMP(3),
        {
          paramType: Encoding.None,
          operator: Operator.Or,
          children: [DUMMY_COMP(0), DUMMY_COMP(1)],
        },
      ],
    })
  })

  it("prunes equal branches in ANDs", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [DUMMY_COMP(0), DUMMY_COMP(0), DUMMY_COMP(1)],
      })
    ).to.deep.equal({
      paramType: Encoding.None,
      operator: Operator.And,
      children: [DUMMY_COMP(0), DUMMY_COMP(1)],
    })
  })

  it("prunes nested equal branches in ANDs", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [
          DUMMY_COMP(0),
          {
            paramType: Encoding.None,
            operator: Operator.And,
            children: [DUMMY_COMP(0), DUMMY_COMP(1)],
          },
          DUMMY_COMP(1),
        ],
      })
    ).to.deep.equal({
      paramType: Encoding.None,
      operator: Operator.And,
      children: [DUMMY_COMP(0), DUMMY_COMP(1)],
    })
  })

  it("prunes single-child ANDs", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [DUMMY_COMP(0)],
      })
    ).to.deep.equal(DUMMY_COMP(0))
  })

  it("prunes ANDs that become single child due to equal branch pruning", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [
          DUMMY_COMP(0),
          {
            paramType: Encoding.None,
            operator: Operator.And,
            children: [DUMMY_COMP(0)],
          },
        ],
      })
    ).to.deep.equal(DUMMY_COMP(0))
  })

  it("enforces a canonical order for children in ANDs", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [DUMMY_COMP(0), DUMMY_COMP(1), DUMMY_COMP(2)],
      })
    ).to.deep.equal(
      normalizeCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [DUMMY_COMP(2), DUMMY_COMP(0), DUMMY_COMP(1)],
      })
    )
  })

  it("prunes trailing Static Pass nodes on AbiEncoded", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          DUMMY_COMP(0),
          { paramType: Encoding.Static, operator: Operator.Pass },
          { paramType: Encoding.Static, operator: Operator.Pass },
        ],
      })
    ).to.deep.equal({
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [DUMMY_COMP(0)],
    })
  })

  it("prunes trailing Static Pass nodes on AbiEncoded", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          DUMMY_COMP(0),
          { paramType: Encoding.Static, operator: Operator.Pass },
          { paramType: Encoding.Static, operator: Operator.Pass },
        ],
      })
    ).to.deep.equal({
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [DUMMY_COMP(0)],
    })
  })

  it("prunes trailing Static Pass nodes on dynamic tuples", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.Tuple,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Dynamic,
            operator: Operator.EqualToAvatar,
          },
          { paramType: Encoding.Static, operator: Operator.Pass },
          { paramType: Encoding.Static, operator: Operator.Pass },
        ],
      })
    ).to.deep.equal({
      paramType: Encoding.Tuple,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Dynamic,
          operator: Operator.EqualToAvatar,
        },
      ],
    })
  })

  it("prunes trailing static Tuple Pass nodes", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          DUMMY_COMP(0),
          {
            paramType: Encoding.Tuple,
            operator: Operator.Pass,
            children: [
              {
                paramType: Encoding.Static,
                operator: Operator.Pass,
              },
            ],
          },
        ],
      })
    ).to.deep.equal({
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [DUMMY_COMP(0)],
    })
  })

  it("does not prune trailing Static Pass nodes on static tuples", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Tuple,
            operator: Operator.Matches,
            children: [
              DUMMY_COMP(0),
              { paramType: Encoding.Static, operator: Operator.Pass },
              { paramType: Encoding.Static, operator: Operator.Pass },
            ],
          },
          DUMMY_COMP(1),
        ],
      })
    ).to.deep.equal({
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Tuple,
          operator: Operator.Matches,
          children: [
            DUMMY_COMP(0),
            { paramType: Encoding.Static, operator: Operator.Pass },
            { paramType: Encoding.Static, operator: Operator.Pass },
          ],
        },
        DUMMY_COMP(1),
      ],
    })
  })

  it("prunes even dynamic trailing Pass nodes on the toplevel Matches", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.EqualToAvatar,
          },
          { paramType: Encoding.Static, operator: Operator.Pass },
          { paramType: Encoding.Dynamic, operator: Operator.Pass },
        ],
      })
    ).to.deep.equal({
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Static,
          operator: Operator.EqualToAvatar,
        },
      ],
    })
  })

  it("keeps CallWithinAllowance (moving it to the end) while pruning trailing Pass nodes on AbiEncoded.Matches", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.None,
            operator: Operator.CallWithinAllowance,
            compValue: encodeKey("test-allowance"),
          },
          {
            paramType: Encoding.Static,
            operator: Operator.Pass,
          },
          {
            paramType: Encoding.Static,
            operator: Operator.Pass,
          },
        ],
      })
    ).to.deep.equal({
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          // first child is always kept
          paramType: Encoding.Static,
          operator: Operator.Pass,
        },
        {
          paramType: Encoding.None,
          operator: Operator.CallWithinAllowance,
          compValue: encodeKey("test-allowance"),
        },
      ],
    })
  })

  it("does not change the position of children other than CallWithinAllowance", async () => {
    const condition = {
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.None,
          operator: Operator.Or,
          children: [DUMMY_COMP(0), DUMMY_COMP(1)],
        },
        DUMMY_COMP(2),
      ],
    }
    expect(normalizeCondition(condition)).to.deep.equal(condition)
  })

  it("adds trailing Pass nodes to make logical branches' type trees compatible", () => {
    expect(
      normalizeCondition({
        paramType: Encoding.None,
        operator: Operator.Or,
        children: [
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [DUMMY_COMP(3)],
          },
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [DUMMY_COMP(0), DUMMY_COMP(1)],
          },
        ],
      })
    ).to.deep.equal({
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [
        {
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            DUMMY_COMP(3),
            { paramType: Encoding.Static, operator: Operator.Pass },
          ],
        },
        {
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [DUMMY_COMP(0), DUMMY_COMP(1)],
        },
      ],
    })
  })

  it("pushes down ORs in function variants differing only in a single param scoping", () => {
    const {
      permissions: [functionVariants],
    } = mergePermissions([
      allow.mainnet.lido.stETH.transfer(
        "0xabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd"
      ),
      allow.mainnet.lido.stETH.transfer(
        "0x1234123412341234123412341234123412341234"
      ),
    ])
    const { condition } = functionVariants as FunctionPermissionCoerced

    expect(normalizeCondition(condition!)).to.deep.equal({
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.None,
          operator: Operator.Or,
          children: [
            {
              operator: Operator.EqualTo,
              paramType: Encoding.Static,
              compValue:
                "0x0000000000000000000000001234123412341234123412341234123412341234",
            },
            {
              operator: Operator.EqualTo,
              paramType: Encoding.Static,
              compValue:
                "0x000000000000000000000000abcdabcdabcdabcdabcdabcdabcdabcdabcdabcd",
            },
          ],
        },
      ],
    })
  })

  it("does not change logical operator semantics when pushing down ORs", () => {
    const {
      permissions: [functionVariants],
    } = mergePermissions([
      allow.mainnet.lido.stETH.transfer(
        "0xabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd",
        c.lt(1000)
      ),
      allow.mainnet.lido.stETH.transfer(
        "0x1234123412341234123412341234123412341234",
        c.lt(2000)
      ),
    ])
    const { condition } = functionVariants as FunctionPermissionCoerced

    expect(normalizeCondition(condition!)).to.deep.equal({
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [
        {
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue:
                "0x0000000000000000000000001234123412341234123412341234123412341234",
            },
            {
              paramType: Encoding.Static,
              operator: Operator.LessThan,
              compValue:
                "0x00000000000000000000000000000000000000000000000000000000000007d0",
            },
          ],
        },
        {
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.EqualTo,
              compValue:
                "0x000000000000000000000000abcdabcdabcdabcdabcdabcdabcdabcdabcdabcd",
            },
            {
              paramType: Encoding.Static,
              operator: Operator.LessThan,
              compValue:
                "0x00000000000000000000000000000000000000000000000000000000000003e8",
            },
          ],
        },
      ],
    })
  })

  it("keeps all other normalizations when pushing down ORs (idempotency is preserved)", () => {
    const {
      permissions: [functionVariants],
    } = mergePermissions([
      // by using a greater number of branches we increase likelihood of differences in the normalized branch orders
      allow.mainnet.lido.stETH.transfer(
        "0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f"
      ),
      allow.mainnet.lido.stETH.transfer(
        "0x1234123412341234123412341234123412341234"
      ),
      allow.mainnet.lido.stETH.transfer(
        "0x9876987698769876987698769876987698769876"
      ),
      allow.mainnet.lido.stETH.transfer(
        "0xabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd"
      ),
      allow.mainnet.lido.stETH.transfer(
        "0xdef1def1def1def1def1def1def1def1def1def1"
      ),
    ])
    const { condition } = functionVariants as FunctionPermissionCoerced

    const normalized = normalizeCondition(condition!)

    // assert idempotency
    expect(normalizeCondition(normalized)).to.deep.equal(normalized)
  })

  it("handles matches on arrays correctly when pushing down ORs", () => {
    const PASS = {
      paramType: Encoding.Static,
      operator: Operator.Pass,
    }
    const condition = {
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [
        {
          paramType: Encoding.Array,
          operator: Operator.Matches,
          children: [DUMMY_COMP(0), PASS, DUMMY_COMP(1)],
        },
        {
          paramType: Encoding.Array,
          operator: Operator.Matches,
          children: [DUMMY_COMP(0), PASS, PASS, DUMMY_COMP(1)],
        },
      ],
    }

    expect(normalizeCondition(condition)).to.deep.equal(condition)
  })
})

suite("normalizeCondition() - MISC transfered from other tests", () => {
  it("both with condition - joined via OR", () => {
    const condition = {
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [DUMMY_COMP(1), DUMMY_COMP(2)],
    }
    expect(normalizeCondition(condition)).to.deep.equal(condition)
  })

  it("both with condition - joined via OR, left gets hoisted", () => {
    const left = {
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [DUMMY_COMP(1), DUMMY_COMP(2)],
    }

    const right = DUMMY_COMP(3)

    const condition = {
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [left, right],
    }

    expect(normalizeCondition(condition)).to.deep.equal({
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [DUMMY_COMP(1), DUMMY_COMP(2), DUMMY_COMP(3)],
    })
  })

  it("both with condition - joined via OR, right gets hoisted", () => {
    const left = DUMMY_COMP(1)

    const right = {
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [DUMMY_COMP(2), DUMMY_COMP(3)],
    }

    const condition = {
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [left, right],
    }

    expect(normalizeCondition(condition)).to.deep.equal({
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [DUMMY_COMP(1), DUMMY_COMP(2), DUMMY_COMP(3)],
    })
  })
})

suite("normalizeConditionDeprecated() - MISC new tests", () => {
  it("DOES NOT transform an AND", () => {
    const C1: Condition = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0x01",
    }

    const C2: Condition = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0x02",
    }

    const condition: Condition = {
      paramType: Encoding.None,
      operator: Operator.And,
      children: [
        {
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [C1],
        },
        {
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [C2],
        },
      ],
    }

    const normalized = normalizeCondition(condition)

    expect(normalized).to.deep.equal(condition)
  })

  it("DOES NOT Transforms an AND, deep", () => {
    const C1: Condition = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0x01",
    }

    const C2: Condition = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0x02",
    }
    const C3: Condition = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0x03",
    }

    const condition: Condition = {
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
              children: [C1, C2],
            },
            {
              paramType: Encoding.Tuple,
              operator: Operator.Matches,
              children: [C1, C3],
            },
          ],
        },
      ],
    }

    const normalized = normalizeCondition(condition)

    // The bug transforms it to:
    expect(normalized).to.deep.equal(condition)
  })

  it("does not push down on arrays: with Array length mismatch", () => {
    const A: Condition = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0x01",
    }

    const B: Condition = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0x02",
    }

    const C: Condition = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0x03",
    }

    // OR of two arrays with DIFFERENT lengths
    const mismatchedArrays: Condition = {
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [
        {
          paramType: Encoding.Array,
          operator: Operator.Matches,
          children: [A, B], // 2 elements
        },
        {
          paramType: Encoding.Array,
          operator: Operator.Matches,
          children: [A, B, C], // 3 elements
        },
      ],
    }

    expect(normalizeCondition(mismatchedArrays)).to.deep.equal(mismatchedArrays)
  })

  it("never pushes down on Arrays", () => {
    const A: Condition = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0x01",
    }

    const B: Condition = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0x02",
    }

    const C: Condition = {
      paramType: Encoding.Static,
      operator: Operator.EqualTo,
      compValue: "0x03",
    }

    // OR of two arrays with DIFFERENT lengths
    const mismatchedArrays: Condition = {
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [
        {
          paramType: Encoding.Array,
          operator: Operator.Matches,
          children: [A, C],
        },
        {
          paramType: Encoding.Array,
          operator: Operator.Matches,
          children: [A, B],
        },
      ],
    }

    expect(normalizeCondition(mismatchedArrays)).to.deep.equal({
      paramType: Encoding.None,
      operator: Operator.Or,
      children: [
        {
          paramType: Encoding.Array,
          operator: Operator.Matches,
          children: [A, B],
        },
        {
          paramType: Encoding.Array,
          operator: Operator.Matches,
          children: [A, C],
        },
      ],
    })
  })
})
