import {
  type Hex,
  type PublicClient,
  type WalletClient,
  concat,
  getCreate2Address,
  parseEther,
  zeroHash,
} from "viem"

export async function deployViaFactory(
  { bytecode, salt = zeroHash }: { bytecode: Hex; salt?: Hex },
  signer: WalletClient,
  publicClient: PublicClient
) {
  const hash = await signer.sendTransaction({
    account: signer.account!,
    chain: signer.chain,
    to: factory.address,
    data: concat([salt, bytecode]),
    value: 0n,
  })
  await publicClient.waitForTransactionReceipt({ hash })

  return getCreate2Address({
    from: factory.address,
    salt,
    bytecode,
  })
}

const factory = {
  address: "0x4e59b44847b379578588920ca78fbf26c0b4956c" as const,
  signerAddress: "0x3fab184622dc19b6109349b94811493bf2a45362" as const,
  transaction:
    "0xf8a58085174876e800830186a08080b853604580600e600039806000f350fe7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03601600081602082378035828234f58015156039578182fd5b8082525050506014600cf31ba02222222222222222222222222222222222222222222222222222222222222222a02222222222222222222222222222222222222222222222222222222222222222" as const,
}

export async function deployFactory(
  signer: WalletClient,
  publicClient: PublicClient
) {
  const { address, signerAddress, transaction } = factory
  // fund the presined transaction signer
  const fundHash = await signer.sendTransaction({
    account: signer.account!,
    chain: signer.chain,
    to: signerAddress,
    value: parseEther("0.01"),
  })
  await publicClient.waitForTransactionReceipt({ hash: fundHash })

  // shoot the presigned transaction
  const deployHash = await publicClient.sendRawTransaction({
    serializedTransaction: transaction,
  })
  await publicClient.waitForTransactionReceipt({ hash: deployHash })

  return address
}
