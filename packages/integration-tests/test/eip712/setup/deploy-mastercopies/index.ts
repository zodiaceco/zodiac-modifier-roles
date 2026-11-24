import type { NetworkConnection } from "hardhat/types/network"
import "@nomicfoundation/hardhat-viem"

import { deployFactory as deploy2470Factory } from "./eip2470.js"
import { deployFallbackHandler } from "./fallbackHandler.js"
import { deployModuleProxyFactory } from "./moduleProxyFactory.js"
import { deployRolesMastercopy } from "./rolesMastercopy.js"
import { deploySafeMastercopy } from "./safeMastercopy.js"
import {
  deploySafeProxyFactory,
  address as safeProxyFactory,
} from "./safeProxyFactory.js"
import { deployFactory } from "./singletonFactory.js"

export default async function deployMastercopies(
  viem: NetworkConnection["viem"]
) {
  const publicClient = await viem.getPublicClient()
  const walletClients = await viem.getWalletClients()
  const deployer = walletClients[6]

  if (await publicClient.getCode({ address: safeProxyFactory })) {
    return
  }

  await deployFactory(deployer, publicClient)
  await deploy2470Factory(deployer, publicClient)
  await deployModuleProxyFactory(deployer, publicClient)
  await deployFallbackHandler(deployer, publicClient)
  await deploySafeMastercopy(deployer, publicClient)
  await deploySafeProxyFactory(deployer, publicClient)
  await deployRolesMastercopy(deployer, publicClient)
}
