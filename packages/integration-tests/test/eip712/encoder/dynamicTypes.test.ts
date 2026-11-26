import { after, describe, it } from "node:test"
import { network } from "hardhat"

import { createCompareToViemHashing } from "./compareToEthersHashing.js"

const connection = await network.create()
const compareToViemHashing = createCompareToViemHashing(connection)

describe("EIP712Encoder", () => {
  after(async () => {
    await connection.close()
  })

  describe("Dynamic Types", () => {
    it("should handle a struct with dynamic types (string, bytes)", async () => {
      const domain = {
        chainId: 1,
        verifyingContract:
          "0x0000000000000000000000000000000000000001" as `0x${string}`,
      }

      const types = {
        NestedStruct: [
          { name: "text", type: "string" },
          { name: "data", type: "bytes" },
        ],
        ParentStruct: [{ name: "items", type: "NestedStruct[]" }],
      }

      await compareToViemHashing({
        domain,
        types,
        message: {
          items: [
            { text: "abc", data: "0xaabbcc" },
            { text: "123", data: "0x112233" },
          ],
        },
      })

      await compareToViemHashing({
        domain,
        types,
        message: {
          items: [
            { text: "abc", data: "0x" },
            { text: "", data: "0x112233" },
            { text: "", data: "0x" },
          ],
        },
      })
    })

    it("should handle nested dynamic types (string inside struct inside struct)", async () => {
      const domain = {
        chainId: 1,
        verifyingContract:
          "0x0000000000000000000000000000000000000001" as `0x${string}`,
      }

      const types = {
        DynamicStruct: [
          { name: "counter", type: "uint256" },
          { name: "text", type: "string" },
          { name: "data", type: "bytes" },
        ],
        NestedStruct: [{ name: "nested", type: "DynamicStruct" }],
        ParentStruct: [{ name: "item", type: "NestedStruct" }],
      }

      await compareToViemHashing({
        domain,
        types,
        message: {
          item: { nested: { counter: 1, text: "abc", data: "0xaabbcc" } },
        },
      })

      await compareToViemHashing({
        domain,
        types,
        message: {
          item: {
            nested: { counter: 99282398, text: "", data: "0x112233" },
          },
        },
      })

      await compareToViemHashing({
        domain,
        types,
        message: {
          item: {
            nested: { counter: 99282398, text: "11", data: "0x" },
          },
        },
      })
    })

    it("should handle nested dynamic types (string inside struct inside array)", async () => {
      const domain = {
        chainId: 1,
        verifyingContract:
          "0x0000000000000000000000000000000000000001" as `0x${string}`,
      }

      const types = {
        DynamicStruct: [
          { name: "text", type: "string" },
          { name: "data", type: "bytes" },
        ],
        NestedStruct: [{ name: "nested", type: "DynamicStruct" }],
        ParentStruct: [{ name: "items", type: "NestedStruct[]" }],
      }

      await compareToViemHashing({
        domain,
        types,
        message: {
          items: [
            { nested: { text: "abc", data: "0xaabbcc" } },
            { nested: { text: "123", data: "0x112233" } },
          ],
        },
      })

      await compareToViemHashing({
        domain,
        types,
        message: {
          items: [
            { nested: { text: "abc", data: "0x" } },
            { nested: { text: "", data: "0x112233" } },
          ],
        },
      })

      await compareToViemHashing({
        domain,
        types,
        message: { items: [] },
      })
    })
  })
})
