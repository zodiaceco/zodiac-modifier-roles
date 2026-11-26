import type { EIP1193Provider } from "@gnosis-guild/zodiac-core";
import type { WalletClient } from "viem";
import type { EthereumProvider } from "hardhat/types/providers";

type TxParams = {
  to?: `0x${string}`;
  data?: `0x${string}`;
  value?: `0x${string}` | bigint;
  gas?: `0x${string}` | bigint;
  gasLimit?: `0x${string}` | bigint | number;
};

export function createEIP1193(
  provider: EthereumProvider,
  walletClient: WalletClient,
): EIP1193Provider {
  return {
    request: async ({ method, params }) => {
      if (method === "eth_sendTransaction") {
        const [{ to, data, value, gas, gasLimit }] = params as [TxParams];
        const resolvedGas = gas ?? gasLimit;
        return walletClient.sendTransaction({
          account: walletClient.account!,
          chain: walletClient.chain,
          to,
          data,
          value: value !== undefined ? BigInt(value) : undefined,
          gas: resolvedGas !== undefined ? BigInt(resolvedGas) : undefined,
        });
      }

      return provider.request({ method, params });
    },
  };
}
