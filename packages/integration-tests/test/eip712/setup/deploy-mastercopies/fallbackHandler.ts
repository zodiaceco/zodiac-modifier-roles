import Artifact from "@safe-global/safe-contracts/build/artifacts/contracts/handler/CompatibilityFallbackHandler.sol/CompatibilityFallbackHandler.json" with { type: "json" }
import type { Hex, PublicClient, WalletClient } from "viem"

import { deployViaFactory } from "./singletonFactory.js"

export const abi = Artifact.abi
export const address = "0xcB4a8d3609A7CCa2D9c063a742f75c899BF2f7b5" as const

export async function deployFallbackHandler(
  signer: WalletClient,
  publicClient: PublicClient
) {
  await deployViaFactory(
    { bytecode: Artifact.bytecode as Hex },
    signer,
    publicClient
  )
  // console.log("fallback: " + address);
}
