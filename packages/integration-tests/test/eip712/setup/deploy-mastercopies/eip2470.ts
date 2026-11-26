import {
  type Address,
  type Hex,
  type PublicClient,
  type WalletClient,
  getCreate2Address,
  parseAbi,
  parseEther,
  zeroHash,
} from "viem"

const deployAbi = parseAbi([
  "function deploy(bytes _initCode, bytes32 _salt) returns (address createdContract)",
])

export async function deployViaFactory(
  { bytecode, salt = zeroHash }: { bytecode: Hex; salt?: Hex },
  deployer: WalletClient,
  publicClient: PublicClient,
  displayName?: string
): Promise<Address> {
  const computedAddress = getCreate2Address({
    from: factoryInfo.address,
    salt,
    bytecode,
  })

  if (!(await publicClient.getCode({ address: computedAddress }))) {
    const hash = await deployer.writeContract({
      address: factoryInfo.address,
      abi: deployAbi,
      functionName: "deploy",
      args: [bytecode, salt],
      gas: 10_000_000n,
      account: deployer.account!,
      chain: deployer.chain,
    })
    const receipt = await publicClient.waitForTransactionReceipt({ hash })

    if (receipt.status !== "success") {
      throw new Error(
        `Couldn't deploy ${displayName || "contract"} eip-2470 factory`
      )
    }
  }

  return computedAddress
}

const factoryInfo = {
  address: "0xce0042b868300000d44a59004da54a005ffdcf9f" as const,
  deployer: "0xBb6e024b9cFFACB947A71991E386681B1Cd1477D" as const,
  transaction:
    "0xf9016c8085174876e8008303c4d88080b90154608060405234801561001057600080fd5b50610134806100206000396000f3fe6080604052348015600f57600080fd5b506004361060285760003560e01c80634af63f0214602d575b600080fd5b60cf60048036036040811015604157600080fd5b810190602081018135640100000000811115605b57600080fd5b820183602082011115606c57600080fd5b80359060200191846001830284011164010000000083111715608d57600080fd5b91908080601f016020809104026020016040519081016040528093929190818152602001838380828437600092019190915250929550509135925060eb915050565b604080516001600160a01b039092168252519081900360200190f35b6000818351602085016000f5939250505056fea26469706673582212206b44f8a82cb6b156bfcc3dc6aadd6df4eefd204bc928a4397fd15dacf6d5320564736f6c634300060200331b83247000822470" as const,
}

/**
 * If it is not deployed on the network, deploys the singleton factory contract
 *
 * https://eips.ethereum.org/EIPS/eip-2470
 */
export async function deployFactory(
  deployer: WalletClient,
  publicClient: PublicClient
) {
  const { address, deployer: factoryDeployer } = factoryInfo

  // fund the singleton factory deployer account
  const fundHash = await deployer.sendTransaction({
    account: deployer.account!,
    chain: deployer.chain,
    to: factoryDeployer,
    value: parseEther("0.0247"),
  })
  await publicClient.waitForTransactionReceipt({ hash: fundHash })

  // deploy the singleton factory
  const deployHash = await publicClient.sendRawTransaction({
    serializedTransaction: factoryInfo.transaction,
  })
  await publicClient.waitForTransactionReceipt({ hash: deployHash })

  return address
}
