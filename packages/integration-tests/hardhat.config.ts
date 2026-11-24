import { defineConfig } from "hardhat/config";
import hardhatNetworkHelpers from "@nomicfoundation/hardhat-network-helpers";
import hardhatNodeTestRunner from "@nomicfoundation/hardhat-node-test-runner";
import hardhatViem from "@nomicfoundation/hardhat-viem";
import hardhatViemAssertions from "@nomicfoundation/hardhat-viem-assertions";

import { compiler } from "../evm/solidity.config.js";

export default defineConfig({
  plugins: [
    hardhatViem,
    hardhatViemAssertions,
    hardhatNodeTestRunner,
    hardhatNetworkHelpers,
  ],
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
    ...compiler,
    npmFilesToBuild: [
      "@gnosis-guild/zodiac-core/contracts/factory/ModuleProxyFactory.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/Roles.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/evaluator/Evaluator.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/evaluator/Integrity.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/periphery/signing/SignTypedMessageLib.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/periphery/unwrappers/MultiSendUnwrapper.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/__test__/fixtures/MultiSend.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/__test__/fixtures/TestAvatar.sol",
      "@gnosis-guild/zodiac-core-modifier-roles/contracts/__test__/mocks/MockEIP712Encoder.sol",
    ],
  },
  networks: {
    default: {
      type: "edr-simulated",
      allowUnlimitedContractSize: true,
    },
  },
});
