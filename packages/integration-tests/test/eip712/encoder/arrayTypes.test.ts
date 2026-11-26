import { after, describe, it } from "node:test"
import { network } from "hardhat"

import { createCompareToViemHashing } from "./compareToEthersHashing.js"

const connection = await network.create()
const compareToViemHashing = createCompareToViemHashing(connection)

describe("EIP712Encoder", () => {
  after(async () => {
    await connection.close()
  })

  describe("Array Types", () => {
    it("should hash a struct with arrays of atomic types (fixed length)", async () => {
      const domain = {
        chainId: 1,
      }

      const types = {
        PersonWithArrays: [
          { name: "name", type: "string" },
          { name: "scores", type: "uint256[3]" },
        ],
      }
      const message = {
        name: "Alice",
        scores: [85, 90, 95],
      }

      await compareToViemHashing({
        domain,
        types,
        message,
      })
    })

    it("should hash a struct with arrays of atomic types (dynamic length)", async () => {
      const domain = {
        chainId: 1,
      }

      const types = {
        Person: [
          { name: "name", type: "string" },
          { name: "scores", type: "uint256[]" },
        ],
      }
      const message = {
        name: "Alice",
        scores: [85, 90, 95],
      }

      await compareToViemHashing({
        domain,
        types,
        message,
      })
    })

    it("should hash a struct with arrays of structs (fixed length)", async () => {
      const domain = {
        name: "Array Test",
        version: "1",
        chainId: 1,
        verifyingContract:
          "0xCcCCccccCCCCcCCCCCCcCcCccCcCCCcCcccccccC" as `0x${string}`,
      }

      // Define the types for the EIP-712 structured data
      const types = {
        Person: [
          { name: "name", type: "string" },
          { name: "wallet", type: "address" },
        ],
        Mail: [
          { name: "from", type: "Person" },
          { name: "to", type: "Person[2]" },
          { name: "contents", type: "string" },
          { name: "attachments", type: "Attachment[3]" },
        ],
        Attachment: [
          { name: "filename", type: "string" },
          { name: "filesize", type: "uint256" },
        ],
      }

      // The actual data to be signed
      const message = {
        from: {
          name: "Alice",
          wallet: "0x17F6AD8Ef982297579C203069C1DbfFE4348c372",
        },
        to: [
          {
            name: "Bob",
            wallet: "0x5c6B0f7Bf3E7ce046039Bd8FABdfD3f9F5021678",
          },
          {
            name: "Charlie",
            wallet: "0x03C6FcED478cBbC9a4FAB34eF9f40767739D1Ff7",
          },
        ],
        contents: "Hello, world!",
        attachments: [
          {
            filename: "document.pdf",
            filesize: 1000000,
          },
          {
            filename: "image.jpg",
            filesize: 500000,
          },
          {
            filename: "spreadsheet.xlsx",
            filesize: 750000,
          },
        ],
      }
      await compareToViemHashing({
        domain,
        types,
        message,
      })
    })

    it("should hash a struct with arrays of structs (dynamic length)", async () => {
      const domain = {
        name: "Dynamic Array Test",
        version: "2",
        chainId: 1,
        verifyingContract:
          "0x4B20993Bc481177ec7E8f571ceCaE8A9e22C02db" as `0x${string}`,
      }

      // Define the types for the EIP-712 structured data with dynamic arrays
      const types = {
        Author: [
          { name: "id", type: "uint256" },
          { name: "name", type: "string" },
          { name: "walletAddress", type: "address" },
        ],
        Comment: [
          { name: "text", type: "string" },
          { name: "timestamp", type: "uint256" },
          { name: "commenter", type: "Author" },
        ],
        Article: [
          { name: "title", type: "string" },
          { name: "content", type: "string" },
          { name: "author", type: "Author" },
          { name: "coAuthors", type: "Author[]" },
          { name: "tags", type: "string[]" },
          { name: "comments", type: "Comment[]" },
          { name: "publishDate", type: "uint256" },
        ],
      }

      // The actual data to be signed
      const message = {
        title: "Understanding EIP-712",
        content:
          "This article explains the EIP-712 standard for structured data hashing and signing.",
        author: {
          id: 1,
          name: "David",
          walletAddress: "0x617F2E2fD72FD9D5503197092aC168c91465E7f2",
        },
        coAuthors: [
          {
            id: 2,
            name: "Emma",
            walletAddress: "0x5c6B0f7Bf3E7ce046039Bd8FABdfD3f9F5021678",
          },
          {
            id: 3,
            name: "Frank",
            walletAddress: "0x03C6FcED478cBbC9a4FAB34eF9f40767739D1Ff7",
          },
          {
            id: 4,
            name: "Grace",
            walletAddress: "0x78731D3Ca6b7E34aC0F824c42a7cC18A495cabaB",
          },
        ],
        tags: ["Ethereum", "EIP-712", "Signing", "TypedData", "Web3"],
        comments: [
          {
            text: "Great explanation!",
            timestamp: 1677683200,
            commenter: {
              id: 5,
              name: "Harper",
              walletAddress: "0x17F6AD8Ef982297579C203069C1DbfFE4348c372",
            },
          },
          {
            text: "I have a question about implementation details.",
            timestamp: 1677686800,
            commenter: {
              id: 6,
              name: "Ivan",
              walletAddress: "0x4B20993Bc481177ec7E8f571ceCaE8A9e22C02db",
            },
          },
        ],
        publishDate: 1677596400,
      }

      await compareToViemHashing({
        domain,
        types,
        message,
      })
    })

    it("should hash a struct with mixed dynamic and fixed-length arrays of structs", async () => {
      const domain = {
        name: "Mixed Array Test",
        version: "3",
        chainId: 1,
        verifyingContract:
          "0x4B20993Bc481177ec7E8f571ceCaE8A9e22C02db" as `0x${string}`,
      }

      const types = {
        User: [
          { name: "id", type: "uint256" },
          { name: "name", type: "string" },
          { name: "wallet", type: "address" },
          { name: "roles", type: "string[]" },
        ],
        Metadata: [
          { name: "createdAt", type: "uint256" },
          { name: "keywords", type: "string[3]" },
        ],
        Reaction: [
          { name: "emoji", type: "string" },
          { name: "user", type: "User" },
        ],
        Document: [
          { name: "title", type: "string" },
          { name: "body", type: "string" },
          { name: "author", type: "User" },
          { name: "contributors", type: "User[2]" },
          { name: "reviewers", type: "User[]" },
          { name: "metadata", type: "Metadata" },
          { name: "reactions", type: "Reaction[]" },
          { name: "versions", type: "uint256[3]" },
          { name: "tags", type: "string[]" },
        ],
      }

      // The actual data to be signed
      const message = {
        title: "EIP-712: Mixed Array Types",
        body: "This document demonstrates how to use both fixed and dynamic arrays in EIP-712 typed data.",
        author: {
          id: 101,
          name: "Alex",
          wallet: "0x617F2E2fD72FD9D5503197092aC168c91465E7f2",
          roles: ["admin", "editor", "author"],
        },
        contributors: [
          {
            id: 102,
            name: "Blake",
            wallet: "0x5c6B0f7Bf3E7ce046039Bd8FABdfD3f9F5021678",
            roles: ["editor"],
          },
          {
            id: 103,
            name: "Casey",
            wallet: "0x03C6FcED478cBbC9a4FAB34eF9f40767739D1Ff7",
            roles: ["contributor", "reviewer"],
          },
        ],
        reviewers: [
          {
            id: 104,
            name: "Dana",
            wallet: "0x78731D3Ca6b7E34aC0F824c42a7cC18A495cabaB",
            roles: ["reviewer"],
          },
          {
            id: 105,
            name: "Eli",
            wallet: "0x17F6AD8Ef982297579C203069C1DbfFE4348c372",
            roles: ["reviewer", "editor"],
          },
          {
            id: 106,
            name: "Fran",
            wallet: "0x4B20993Bc481177ec7E8f571ceCaE8A9e22C02db",
            roles: ["reviewer", "legal"],
          },
        ],
        metadata: {
          createdAt: 1677683200,
          keywords: ["Ethereum", "EIP-712", "Arrays"], // Fixed length array (exactly 3)
        },
        reactions: [
          {
            emoji: "👍",
            user: {
              id: 107,
              name: "Gene",
              wallet: "0x617F2E2fD72FD9D5503197092aC168c91465E7f2",
              roles: ["reader"],
            },
          },
          {
            emoji: "🚀",
            user: {
              id: 108,
              name: "Harper",
              wallet: "0x5c6B0f7Bf3E7ce046039Bd8FABdfD3f9F5021678",
              roles: ["reader", "sponsor"],
            },
          },
        ],
        versions: [1, 2, 3],
        tags: ["documentation", "tutorial", "standards", "typed-data"],
      }

      await compareToViemHashing({
        domain,
        types,
        message,
      })
    })
  })
})
