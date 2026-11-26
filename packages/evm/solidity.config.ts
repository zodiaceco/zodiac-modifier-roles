// Compiler version and settings the contracts are built with. Shared with
// packages/integration-tests, which compiles the same sources.
export const compiler = {
  version: "0.8.38",
  settings: {
    evmVersion: "cancun",
    optimizer: {
      enabled: true,
      runs: 10,
    },
  },
};
