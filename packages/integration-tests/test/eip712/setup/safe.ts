import {
  type Address,
  type WalletClient,
  concat,
  encodeAbiParameters,
  encodeFunctionData,
  zeroAddress,
  zeroHash,
} from "viem"

import { abi as safeAbi } from "./deploy-mastercopies/safeMastercopy.js"
import {
  calculateSafeAddress,
  populateSafeCreation,
} from "./encodeSafeCreation.js"

export async function deploySafe(
  {
    owners,
    threshold,
    creationNonce,
  }: {
    owners: Address[]
    threshold: number
    creationNonce: bigint | number
  },
  relayer: WalletClient
) {
  const tx = populateSafeCreation({
    owners,
    threshold,
    creationNonce: BigInt(creationNonce),
  })
  await relayer.sendTransaction({
    account: relayer.account!,
    chain: relayer.chain,
    ...tx,
  })

  return calculateSafeAddress({
    owners,
    threshold,
    creationNonce: BigInt(creationNonce),
  })
}

export async function enableModuleInSafe(
  {
    safe,
    module,
  }: {
    safe: Address
    module: Address
  },
  signer: WalletClient
) {
  return signer.sendTransaction({
    account: signer.account!,
    chain: signer.chain,
    to: safe,
    data: encodeFunctionData({
      abi: safeAbi,
      functionName: "execTransaction",
      args: [
        safe,
        0n,
        encodeFunctionData({
          abi: safeAbi,
          functionName: "enableModule",
          args: [module],
        }),
        0,
        0n,
        0n,
        0n,
        zeroAddress,
        zeroAddress,
        createPreApprovedSignature(signer.account!.address),
      ],
    }),
  })
}

const createPreApprovedSignature = (approver: Address) => {
  return concat([
    encodeAbiParameters([{ type: "address" }], [approver]),
    zeroHash,
    "0x01",
  ])
}
