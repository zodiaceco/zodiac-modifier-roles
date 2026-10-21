import dotenv from "dotenv";
import { defineConfig } from "hardhat/config";
import hardhatToolboxMochaEthers from "@nomicfoundation/hardhat-toolbox-mocha-ethers";

import deployMastercopy from "./tasks/deploy-mastercopy.js";
import verifyMastercopy from "./tasks/verify-mastercopy.js";

dotenv.config();

const { INFURA_KEY, PK, MNEMONIC, ETHERSCAN_API_KEY } = process.env;

const accounts = PK
  ? [PK]
  : {
      mnemonic:
        MNEMONIC ||
        "candy maple cake sugar pudding cream honey rich smooth crumble sweet treat",
    };

export default defineConfig({
  plugins: [hardhatToolboxMochaEthers],
  paths: {
    artifacts: "build/artifacts",
    cache: "build/cache",
    sources: "contracts",
  },
  solidity: {
    version: "0.8.37",
    settings: {
      evmVersion: "cancun",
      viaIR: true,
      optimizer: {
        enabled: true,
        runs: 10,
      },
    },
    npmFilesToBuild: [
      "@gnosis-guild/zodiac-core/contracts/factory/ModuleProxyFactory.sol",
    ],
  },
  typechain: {
    outDir: "typechain-types",
    tsNocheck: true,
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
  verify: {
    etherscan: {
      apiKey: ETHERSCAN_API_KEY ?? "",
      enabled: true,
    },
    sourcify: {
      enabled: false,
    },
  },
  tasks: [deployMastercopy, verifyMastercopy],
});
