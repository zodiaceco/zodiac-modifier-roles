import Artifact from "@safe-global/safe-contracts/build/artifacts/contracts/proxies/SafeProxyFactory.sol/SafeProxyFactory.json" with { type: "json" }
import type { Hex, PublicClient, WalletClient } from "viem"

import { deployViaFactory } from "./singletonFactory.js"

export const abi = Artifact.abi
export const address = "0xd9d2Ba03a7754250FDD71333F444636471CACBC4" as const

export async function deploySafeProxyFactory(
  signer: WalletClient,
  publicClient: PublicClient
) {
  await deployViaFactory(
    { bytecode: Artifact.bytecode as Hex },
    signer,
    publicClient
  )
}
