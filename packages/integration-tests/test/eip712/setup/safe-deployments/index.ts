import {
  type Address,
  type Hex,
  type PublicClient,
  type WalletClient,
  concat,
  getAddress,
  getCreate2Address,
  keccak256,
  parseAbi,
  zeroHash,
} from "viem"

import v1_3_0 from "./v1.3.0.js"
import v1_4_1 from "./v1.4.1.js"
import v1_5_0 from "./v1.5.0.js"

export type SafeVersion = "1.3.0" | "1.4.1" | "1.5.0"

type SafeContract = { address: Address; codeHash: Hex; creationCode: Hex }

export type SafeDeployment = {
  version: SafeVersion
  /** The deterministic deployment proxy, or the Safe singleton factory */
  factory: Address
  singleton: SafeContract
  proxyFactory: SafeContract
  compatibilityFallbackHandler: SafeContract
  extensibleFallbackHandler?: SafeContract
  proxyCreationCode: Hex
}

export const safeDeployments: Record<SafeVersion, SafeDeployment> = {
  "1.3.0": v1_3_0,
  "1.4.1": v1_4_1,
  "1.5.0": v1_5_0,
}

/** The functions the tests call, the same in every version. */
export const safeAbi = parseAbi([
  "function setup(address[] _owners, uint256 _threshold, address to, bytes data, address fallbackHandler, address paymentToken, uint256 payment, address paymentReceiver)",
  "function execTransaction(address to, uint256 value, bytes data, uint8 operation, uint256 safeTxGas, uint256 baseGas, uint256 gasPrice, address gasToken, address refundReceiver, bytes signatures) payable returns (bool success)",
  "function enableModule(address module)",
  "function domainSeparator() view returns (bytes32)",
])

export const safeProxyFactoryAbi = parseAbi([
  "function createProxyWithNonce(address _singleton, bytes initializer, uint256 saltNonce) returns (address proxy)",
])

/**
 * Deploys the contracts of a Safe version through the factory Safe deployed
 * them with, and checks each is at its canonical address with its canonical
 * runtime code. The factory must already be deployed.
 */
export async function deploySafeContracts(
  version: SafeVersion,
  signer: WalletClient,
  publicClient: PublicClient
) {
  const deployment = safeDeployments[version]
  const { factory } = deployment

  for (const [name, contract] of contractsOf(deployment)) {
    const { address, codeHash, creationCode } = contract
    const label = `Safe ${version} ${name}`

    const computed = getCreate2Address({
      from: factory,
      salt: zeroHash,
      bytecode: creationCode,
    })
    if (computed !== getAddress(address)) {
      throw new Error(`${label}: creation code deploys to ${computed}`)
    }

    if (!(await publicClient.getCode({ address }))) {
      const hash = await signer.sendTransaction({
        account: signer.account!,
        chain: signer.chain,
        to: factory,
        data: concat([zeroHash, creationCode]),
      })
      await publicClient.waitForTransactionReceipt({ hash })
    }

    const code = await publicClient.getCode({ address })
    if (!code || keccak256(code) !== codeHash.toLowerCase()) {
      throw new Error(`${label}: ${address} does not hold the canonical code`)
    }
  }
}

function contractsOf(deployment: SafeDeployment) {
  const {
    singleton,
    proxyFactory,
    compatibilityFallbackHandler,
    extensibleFallbackHandler,
  } = deployment
  return Object.entries({
    singleton,
    proxyFactory,
    compatibilityFallbackHandler,
    ...(extensibleFallbackHandler && { extensibleFallbackHandler }),
  })
}
