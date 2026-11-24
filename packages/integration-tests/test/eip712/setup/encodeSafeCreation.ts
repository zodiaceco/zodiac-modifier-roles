import SafeProxyArtifact from "@safe-global/safe-contracts/build/artifacts/contracts/proxies/SafeProxy.sol/SafeProxy.json" with { type: "json" }
import {
  type Address,
  type Hex,
  concat,
  encodeAbiParameters,
  encodeFunctionData,
  getCreate2Address,
  keccak256,
  zeroAddress,
} from "viem"

import { address as fallbackHandler } from "./deploy-mastercopies/fallbackHandler.js"
import {
  abi as safeAbi,
  address as mastercopy,
} from "./deploy-mastercopies/safeMastercopy.js"
import {
  abi as factoryAbi,
  address as factory,
} from "./deploy-mastercopies/safeProxyFactory.js"

const creationBytecode = SafeProxyArtifact.bytecode as Hex

export function calculateSafeAddress({
  owners,
  threshold,
  creationNonce,
}: {
  owners: Address[]
  threshold: number
  creationNonce: bigint | number
}): Address {
  const salt = keccak256(
    concat([
      keccak256(initializer({ owners, threshold })),
      encodeAbiParameters([{ type: "uint256" }], [BigInt(creationNonce)]),
    ])
  )

  const deploymentData = concat([
    creationBytecode,
    encodeAbiParameters([{ type: "address" }], [mastercopy]),
  ])

  return getCreate2Address({
    from: factory,
    salt,
    bytecode: deploymentData,
  })
}

export function populateSafeCreation({
  owners,
  threshold,
  creationNonce,
}: {
  owners: Address[]
  threshold: number
  creationNonce: bigint
}) {
  return {
    to: factory,
    value: 0n,
    data: encodeFunctionData({
      abi: factoryAbi,
      functionName: "createProxyWithNonce",
      args: [mastercopy, initializer({ owners, threshold }), creationNonce],
    }),
  }
}

function initializer({
  owners,
  threshold,
}: {
  owners: Address[]
  threshold: number
}) {
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
