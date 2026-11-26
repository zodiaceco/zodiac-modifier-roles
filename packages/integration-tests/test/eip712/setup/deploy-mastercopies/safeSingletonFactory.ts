import { type PublicClient, type WalletClient, parseEther } from "viem"

/**
 * The Safe singleton factory (github.com/safe-global/safe-singleton-factory),
 * which deploys Safe 1.4.1 and later at their canonical addresses. Same code
 * as the deterministic deployment proxy: calldata is `salt ‖ creationCode`.
 * The presigned transaction is the one for chain 31337.
 */
export const factory = {
  address: "0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7" as const,
  signerAddress: "0xE1CB04A0fA36DdD16a06ea828007E35e1a3cBC37" as const,
  transaction:
    "0xf8a78085174876e800830186a08080b853604580600e600039806000f350fe7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03601600081602082378035828234f58015156039578182fd5b8082525050506014600cf382f4f5a00dc4d1d21b308094a30f5f93da35e4d72e99115378f135f2295bea47301a3165a0636b822daad40aa8c52dd5132f378c0c0e6d83b4898228c7e21c84e631a0b891" as const,
}

export async function deploySafeSingletonFactory(
  signer: WalletClient,
  publicClient: PublicClient
) {
  const { address, signerAddress, transaction } = factory
  // fund the presigned transaction signer (gas price 100 gwei, gas 100k)
  const fundHash = await signer.sendTransaction({
    account: signer.account!,
    chain: signer.chain,
    to: signerAddress,
    value: parseEther("0.01"),
  })
  await publicClient.waitForTransactionReceipt({ hash: fundHash })

  const deployHash = await publicClient.sendRawTransaction({
    serializedTransaction: transaction,
  })
  await publicClient.waitForTransactionReceipt({ hash: deployHash })

  return address
}
