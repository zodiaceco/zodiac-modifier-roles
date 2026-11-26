import {
  type Address,
  type WalletClient,
  concat,
  encodeAbiParameters,
  encodeFunctionData,
  zeroAddress,
  zeroHash,
} from "viem"

import {
  type SafeCreation,
  calculateSafeAddress,
  populateSafeCreation,
} from "./encodeSafeCreation.js"
import { safeAbi } from "./safe-deployments/index.js"

/** Creates a Safe (1.4.1 unless `version` says otherwise) and returns its address. */
export async function deploySafe(
  creation: SafeCreation,
  relayer: WalletClient
) {
  await relayer.sendTransaction({
    account: relayer.account!,
    chain: relayer.chain,
    ...populateSafeCreation(creation),
  })

  return calculateSafeAddress(creation)
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
