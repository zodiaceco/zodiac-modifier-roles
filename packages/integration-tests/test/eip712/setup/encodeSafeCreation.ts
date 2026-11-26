import {
  type Address,
  concat,
  encodeAbiParameters,
  encodeFunctionData,
  getCreate2Address,
  keccak256,
  zeroAddress,
} from "viem"

import {
  type SafeVersion,
  safeAbi,
  safeDeployments,
  safeProxyFactoryAbi,
} from "./safe-deployments/index.js"

export type SafeCreation = {
  owners: Address[]
  threshold: number
  creationNonce: bigint | number
  /** Safe 1.4.1 by default */
  version?: SafeVersion
  /** The version's CompatibilityFallbackHandler by default */
  fallbackHandler?: Address
}

export function calculateSafeAddress(creation: SafeCreation): Address {
  const { singleton, proxyFactory, proxyCreationCode } =
    safeDeployments[creation.version ?? "1.4.1"]

  const salt = keccak256(
    concat([
      keccak256(initializer(creation)),
      encodeAbiParameters(
        [{ type: "uint256" }],
        [BigInt(creation.creationNonce)]
      ),
    ])
  )

  return getCreate2Address({
    from: proxyFactory.address,
    salt,
    bytecode: concat([
      proxyCreationCode,
      encodeAbiParameters([{ type: "address" }], [singleton.address]),
    ]),
  })
}

export function populateSafeCreation(creation: SafeCreation) {
  const { singleton, proxyFactory } =
    safeDeployments[creation.version ?? "1.4.1"]

  return {
    to: proxyFactory.address,
    value: 0n,
    data: encodeFunctionData({
      abi: safeProxyFactoryAbi,
      functionName: "createProxyWithNonce",
      args: [
        singleton.address,
        initializer(creation),
        BigInt(creation.creationNonce),
      ],
    }),
  }
}

function initializer({
  owners,
  threshold,
  version = "1.4.1",
  fallbackHandler = safeDeployments[version].compatibilityFallbackHandler
    .address,
}: SafeCreation) {
  return encodeFunctionData({
    abi: safeAbi,
    functionName: "setup",
    args: [
      owners,
      BigInt(threshold),
      zeroAddress,
      "0x",
      fallbackHandler,
      zeroAddress,
      0n,
      zeroAddress,
    ],
  })
}
