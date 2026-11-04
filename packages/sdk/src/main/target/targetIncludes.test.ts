import { expect, it, describe } from "vitest"
import {
  Encoding,
  Clearance,
  Condition,
  ExecutionOptions,
  Operator,
  Target,
} from "../types"

import { abiEncode } from "../abiEncode"
import { targetIncludes } from "./targetIncludes"

const AddressOne = "0x0000000000000000000000000000000000000001"

const COMP = (id: number) => ({
  paramType: Encoding.Static,
  operator: Operator.EqualTo,
  compValue: abiEncode(["uint256"], [id]),
})

describe("targetIncludes()", () => {
  describe("Execution options", () => {
    it("target without send cannot include target with send", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.None,
            functions: [],
          },
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.Send,
            functions: [],
          }
        )
      ).toBe(false)

      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.DelegateCall,
            functions: [],
          },
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.Both,
            functions: [],
          }
        )
      ).toBe(false)
    })

    it("target with send includes target without send", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.Send,
            functions: [],
          },
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.None,
            functions: [],
          }
        )
      ).toBe(true)

      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.Both,
            functions: [],
          },
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.Send,
            functions: [],
          }
        )
      ).toBe(true)
    })

    it("target without delegatecall cannot include target with delegatecall", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.None,
            functions: [],
          },
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.DelegateCall,
            functions: [],
          }
        )
      ).toBe(false)

      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.Send,
            functions: [],
          },
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.Both,
            functions: [],
          }
        )
      ).toBe(false)
    })

    it("target with delegatecall includes target without delegatecall", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.DelegateCall,
            functions: [],
          },
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.None,
            functions: [],
          }
        )
      ).toBe(true)

      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.Both,
            functions: [],
          },
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.DelegateCall,
            functions: [],
          }
        )
      ).toBe(true)
    })
  })

  describe("Clearance levels", () => {
    it("allowed includes everything", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.None,
            functions: [],
          },
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.None,
            functions: [],
          }
        )
      ).toBe(true)

      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.None,
            functions: [],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          }
        )
      ).toBe(true)

      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.None,
            functions: [],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: COMP(1),
              },
            ],
          }
        )
      ).toBe(true)
    })

    it("function clearance does NOT include target clearance", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.None,
            functions: [],
          }
        )
      ).toBe(false)
    })
  })

  describe("Wildcard functions", () => {
    it("wildcard includes wildcard with same selector", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          }
        )
      ).toBe(true)
    })

    it("wildcard does NOT include wildcard with different selector", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x02",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          }
        )
      ).toBe(false)
    })

    it("wildcard includes conditional with same selector", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: COMP(1),
              },
            ],
          }
        )
      ).toBe(true)
    })

    it("wildcard does NOT include conditional with different selector", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x02",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: COMP(1),
              },
            ],
          }
        )
      ).toBe(false)
    })

    it("conditional does NOT include wildcard", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: COMP(1),
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          }
        )
      ).toBe(false)
    })
  })

  describe("Conditional functions", () => {
    it("conditional includes identical conditional", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: COMP(1),
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: COMP(1),
              },
            ],
          }
        )
      ).toBe(true)
    })

    it("conditional does NOT include different conditional", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: COMP(1),
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: COMP(2),
              },
            ],
          }
        )
      ).toBe(false)
    })

    it("conditional does NOT include conditional with different selector", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: COMP(1),
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x02",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: COMP(1),
              },
            ],
          }
        )
      ).toBe(false)
    })

    it("conditions are normalized before comparison", () => {
      // Test that equivalent but differently structured conditions are considered equal
      const condition1: Condition = {
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        compValue: "0x",
        children: [
          COMP(2),
          COMP(1),
          {
            compValue: "0x",
            paramType: Encoding.Static,
            operator: Operator.Pass,
          },
        ],
      }

      // the same condition without the empty compValues (a trailing Pass is
      // kept: it changes which calldata the contract accepts)
      const condition2: Condition = {
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          COMP(2),
          COMP(1),
          { paramType: Encoding.Static, operator: Operator.Pass },
        ],
      }

      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: condition1,
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: condition2,
              },
            ],
          }
        )
      ).toBe(true)
    })

    it("conditional includes subset conditional (OR variant)", () => {
      // Left condition has OR(1, 2, 3), right has OR(1, 2) - should include
      const leftCondition: Condition = {
        paramType: Encoding.None,
        operator: Operator.Or,
        children: [COMP(1), COMP(2), COMP(3)],
      }

      const rightCondition: Condition = {
        paramType: Encoding.None,
        operator: Operator.Or,
        children: [COMP(1), COMP(2)],
      }

      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: leftCondition,
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: rightCondition,
              },
            ],
          }
        )
      ).toBe(true)
    })

    it("conditional does NOT include superset conditional", () => {
      // Left condition has OR(1, 2), right has OR(1, 2, 3) - should NOT include
      const leftCondition: Condition = {
        paramType: Encoding.None,
        operator: Operator.Or,
        children: [COMP(1), COMP(2)],
      }

      const rightCondition: Condition = {
        paramType: Encoding.None,
        operator: Operator.Or,
        children: [COMP(1), COMP(2), COMP(3)],
      }

      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: leftCondition,
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: rightCondition,
              },
            ],
          }
        )
      ).toBe(false)
    })
  })

  describe("Multiple functions", () => {
    it("target with multiple functions includes target with subset", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
              {
                selector: "0x02",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          }
        )
      ).toBe(true)
    })

    it("target does NOT include function not present", () => {
      expect(
        targetIncludes(
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          },
          {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x02",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          }
        )
      ).toBe(false)
    })
  })

  describe("Clearance type matrix", () => {
    const matrix = [
      // [p1_type, p2_type, expected]
      ["target", "target", true],
      ["target", "wildcard", true],
      ["target", "conditional", true],
      ["wildcard", "target", false],
      ["wildcard", "wildcard", true], // same selector
      ["wildcard", "conditional", true], // same selector
      ["conditional", "target", false],
      ["conditional", "wildcard", false],
      ["conditional", "conditional", true], // same condition
    ]

    matrix.forEach(([p1Type, p2Type, expected]) => {
      it(`${p1Type} includes ${p2Type}: ${expected}`, () => {
        const p1 = createTarget(p1Type as any)
        const p2 = createTarget(p2Type as any)

        expect(targetIncludes(p1, p2)).toBe(expected)
      })
    })

    function createTarget(type: "target" | "wildcard" | "conditional"): Target {
      switch (type) {
        case "target":
          return {
            address: AddressOne,
            clearance: Clearance.Target,
            executionOptions: ExecutionOptions.None,
            functions: [],
          }
        case "wildcard":
          return {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: true,
              },
            ],
          }
        case "conditional":
          return {
            address: AddressOne,
            clearance: Clearance.Function,
            executionOptions: ExecutionOptions.None,
            functions: [
              {
                selector: "0x01",
                executionOptions: ExecutionOptions.None,
                wildcarded: false,
                condition: COMP(1),
              },
            ],
          }
      }
    }
  })
})
