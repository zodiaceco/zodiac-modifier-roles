import { after, describe, it } from "node:test"
import { network } from "hardhat"

import { createCompareToViemHashing } from "./compareToEthersHashing.js"

const connection = await network.create()
const compareToViemHashing = createCompareToViemHashing(connection)

describe("EIP712Encoder", () => {
  after(async () => {
    await connection.close()
  })

  describe("Static Types", () => {
    const domain = { chainId: 1 }

    it("should handle boolean values", async () => {
      const types = { Person: [{ name: "adult", type: "bool" }] }

      await compareToViemHashing({
        domain,
        types,
        message: { adult: true },
      })

      await compareToViemHashing({
        domain,
        types,
        message: { adult: false },
      })
    })

    it("should handle address values", async () => {
      const types = { Person: [{ name: "address", type: "address" }] }

      await compareToViemHashing({
        domain,
        types,
        message: { address: "0x0000000000000000000000000000000000000000" },
      })

      await compareToViemHashing({
        domain,
        types,
        message: { address: "0x0000000000000000000000000000000000000123" },
      })
    })

    it("should handle bytes1 - bytes32 values", async () => {
      const typesBytes1 = { Person: [{ name: "meta", type: "bytes1" }] }
      const typesBytes16 = { Person: [{ name: "meta", type: "bytes16" }] }
      const typesBytes32 = { Person: [{ name: "meta", type: "bytes32" }] }

      await compareToViemHashing({
        domain,
        types: typesBytes1,
        message: { meta: "0x00" },
      })

      await compareToViemHashing({
        domain,
        types: typesBytes1,
        message: { meta: "0xff" },
      })

      await compareToViemHashing({
        domain,
        types: typesBytes16,
        message: { meta: "0x00000000000000000000000000000000" },
      })

      await compareToViemHashing({
        domain,
        types: typesBytes16,
        message: { meta: "0xf000000000000000000000000000000f" },
      })

      await compareToViemHashing({
        domain,
        types: typesBytes32,
        message: {
          meta: "0x0000000000000000000000000000000000000000000000000000000000000000",
        },
      })

      await compareToViemHashing({
        domain,
        types: typesBytes32,
        message: {
          meta: "0xf000000000000000000000000000000ff000000000000000000000000000000f",
        },
      })
    })
  })
})
