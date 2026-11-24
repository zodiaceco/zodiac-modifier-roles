import { after, describe, it } from "node:test"
import { network } from "hardhat"

import { createCompareToViemHashing } from "./compareToEthersHashing.js"

const connection = await network.create()
const compareToViemHashing = createCompareToViemHashing(connection)

describe("EIP712Encoder", () => {
  after(async () => {
    await connection.close()
  })

  const domain = { chainId: 1 }

  describe("Tuple Types", () => {
    it("should handle a struct with nested static struct", async () => {
      const types = {
        Inner: [
          { name: "amounts", type: "uint256[2]" },
          { name: "recipient", type: "address" },
        ],
        Outer: [
          { name: "inner", type: "Inner" },
          { name: "sender", type: "address" },
        ],
      }

      const message = {
        inner: {
          amounts: [100, 200],
          recipient: "0x1234567890123456789012345678901234567890",
        },
        sender: "0xabcdefabcdefabcdefabcdefabcdefabcdefabcd",
      }

      await compareToViemHashing({
        domain,
        types,
        message,
      })
    })

    it("should handle a struct with nested dynamic struct", async () => {
      const types = {
        Inner: [
          { name: "note", type: "string" },
          { name: "wallet", type: "address" },
        ],
        Outer: [
          { name: "inner", type: "Inner" },
          { name: "amount", type: "uint256" },
        ],
      }

      const message = {
        inner: {
          note: "hello world",
          wallet: "0x1234567890123456789012345678901234567890",
        },
        amount: 420,
      }

      await compareToViemHashing({
        domain,
        types,
        message,
      })
    })

    it("should handle a struct with nested dynamic -> static", async () => {
      const types = {
        Static: [
          { name: "amount", type: "uint256" },
          { name: "wallet", type: "address" },
        ],
        Dynamic: [
          { name: "note", type: "string" },
          { name: "staticData", type: "Static" },
        ],
        Outer: [
          { name: "dynamicData", type: "Dynamic" },
          { name: "deadline", type: "uint256" },
        ],
      }

      const message = {
        dynamicData: {
          note: "dynamic text",
          staticData: {
            amount: 1000,
            wallet: "0x1234567890123456789012345678901234567890",
          },
        },
        deadline: 1717171717,
      }

      await compareToViemHashing({
        domain,
        types,
        message,
      })
    })

    it("should handle a struct with nested dynamic -> dynamic", async () => {
      const types = {
        Dynamic: [
          { name: "note", type: "string" },
          { name: "sender", type: "address" },
        ],
        Middle: [
          { name: "amount", type: "uint256" },
          { name: "dynamicData", type: "Dynamic" },
        ],
        Outer: [
          { name: "staticData", type: "Middle" },
          { name: "nonce", type: "uint256" },
        ],
      }

      const message = {
        staticData: {
          amount: 1337,
          dynamicData: {
            note: "hello dynamic",
            sender: "0x1234567890123456789012345678901234567890",
          },
        },
        nonce: 42,
      }

      await compareToViemHashing({
        domain,
        types,
        message,
      })
    })
  })
})
