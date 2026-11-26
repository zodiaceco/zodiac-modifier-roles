import type { NetworkConnection } from "hardhat/types/network"
import "@nomicfoundation/hardhat-viem"

import {
  type SafeVersion,
  deploySafeContracts,
  safeDeployments,
} from "../safe-deployments/index.js"
import { deployFactory as deploy2470Factory } from "./eip2470.js"
import { deployModuleProxyFactory } from "./moduleProxyFactory.js"
import {
  address as rolesMastercopyAddress,
  deployRolesMastercopy,
} from "./rolesMastercopy.js"
import { deploySafeSingletonFactory } from "./safeSingletonFactory.js"
import { deployFactory } from "./singletonFactory.js"

/**
 * Deploys the factories, Safe 1.3.0, 1.4.1 and 1.5.0 at their canonical
 * addresses, and the Roles mastercopy. Once per network.
 */
export default async function deployMastercopies(
  viem: NetworkConnection["viem"]
) {
  const publicClient = await viem.getPublicClient()
  const walletClients = await viem.getWalletClients()
  const deployer = walletClients[6]

  if (await publicClient.getCode({ address: rolesMastercopyAddress })) {
    return
  }

  await deployFactory(deployer, publicClient)
  await deploySafeSingletonFactory(deployer, publicClient)
  await deploy2470Factory(deployer, publicClient)
  await deployModuleProxyFactory(deployer, publicClient)
  for (const version of Object.keys(safeDeployments) as SafeVersion[]) {
    await deploySafeContracts(version, deployer, publicClient)
  }
  await deployRolesMastercopy(deployer, publicClient)
}
