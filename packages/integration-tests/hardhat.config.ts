import { defineConfig } from "hardhat/config";
import hardhatToolboxMochaEthers from "@nomicfoundation/hardhat-toolbox-mocha-ethers";

export default defineConfig({
  plugins: [hardhatToolboxMochaEthers],
  // Hardhat v3 no longer honors `paths.root` from user config (it's always the
  // directory containing this file). Keep artifacts/cache local so this package
  // and the evm package don't race on the same Hardhat artifact files when
  // `turbo test` runs them in parallel.
  paths: {
    artifacts: "build/artifacts",
    cache: "build/cache",
    sources: "contracts",
    tests: "test",
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
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/Roles.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/core/evaluate/WithinRatioChecker.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/core/serialize/ConditionStorer.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/periphery/signing/SignTypedMessageLib.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/periphery/unwrappers/MultiSendUnwrapper.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/__test__/fixtures/MultiSend.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/__test__/fixtures/TestAvatar.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/__test__/mocks/MockEIP712Encoder.sol",
    ],
  },
  typechain: {
    outDir: "build/typechain-types",
    tsNocheck: true,
  },
  networks: {
    default: {
      type: "edr-simulated",
      allowUnlimitedContractSize: true,
    },
  },
  test: {
    mocha: {
      timeout: 2000000,
    },
  },
});
