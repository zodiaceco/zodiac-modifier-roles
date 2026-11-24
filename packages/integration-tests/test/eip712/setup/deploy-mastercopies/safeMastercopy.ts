import Artifact from "@safe-global/safe-contracts/build/artifacts/contracts/Safe.sol/Safe.json" with { type: "json" }
import type { Hex, PublicClient, WalletClient } from "viem"

import { deployViaFactory } from "./singletonFactory.js"

export const address = "0x639245e8476E03e789a244f279b5843b9633b2E7" as const

export const abi = Artifact.abi

export async function deploySafeMastercopy(
  signer: WalletClient,
  publicClient: PublicClient
) {
  await deployViaFactory(
    { bytecode: Artifact.bytecode as Hex },
    signer,
    publicClient
  )
}
