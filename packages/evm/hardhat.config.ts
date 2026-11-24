import { existsSync } from "node:fs";
// Needed so Hardhat tests importing extensionless CJS/TS files from packages/sdk/src resolve.
import { register as registerTsxCjs } from "tsx/cjs/api";
import { defineConfig } from "hardhat/config";
import hardhatNetworkHelpers from "@nomicfoundation/hardhat-network-helpers";
import hardhatNodeTestRunner from "@nomicfoundation/hardhat-node-test-runner";
import hardhatViem from "@nomicfoundation/hardhat-viem";
import hardhatViemAssertions from "@nomicfoundation/hardhat-viem-assertions";

import { compiler } from "./solidity.config.js";
import deployMastercopy from "./tasks/deploy-mastercopy.js";
import verifyMastercopy from "./tasks/verify-mastercopy.js";

registerTsxCjs();
if (existsSync(".env")) process.loadEnvFile();

const { INFURA_KEY, PK, MNEMONIC } = process.env;

const accounts = PK
  ? [PK]
  : {
      mnemonic:
        MNEMONIC ||
        "candy maple cake sugar pudding cream honey rich smooth crumble sweet treat",
    };

export default defineConfig({
  plugins: [
    hardhatViem,
    hardhatViemAssertions,
    hardhatNodeTestRunner,
    hardhatNetworkHelpers,
  ],
  paths: {
    artifacts: "build/artifacts",
    cache: "build/cache",
    sources: "contracts",
  },
  solidity: {
    ...compiler,
    npmFilesToBuild: [
      "@gnosis-guild/zodiac-core/contracts/factory/ModuleProxyFactory.sol",
    ],
  },
  // Initial release networks; zodiac handles deployment to additional chains.
  networks: {
    default: {
      type: "edr-simulated",
      allowUnlimitedContractSize: true,
      hardfork: "cancun",
    },
    arbitrum: {
      type: "http",
      chainId: 42161,
      accounts,
      url: "https://arb1.arbitrum.io/rpc",
    },
    base: {
      type: "http",
      chainId: 8453,
      accounts,
      url: "https://mainnet.base.org",
    },
    gnosis: {
      type: "http",
      chainId: 100,
      accounts,
      url: "https://rpc.gnosischain.com",
    },
    mainnet: {
      type: "http",
      chainId: 1,
      accounts,
      url: `https://mainnet.infura.io/v3/${INFURA_KEY}`,
    },
    optimism: {
      type: "http",
      chainId: 10,
      accounts,
      url: "https://mainnet.optimism.io",
    },
    sepolia: {
      type: "http",
      chainId: 11155111,
      accounts,
      url: `https://sepolia.infura.io/v3/${INFURA_KEY}`,
    },
  },
  tasks: [deployMastercopy, verifyMastercopy],
});
