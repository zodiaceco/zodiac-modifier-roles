import { defineConfig } from "tsdown"

export default defineConfig([
  {
    entry: {
      index: "./src/main/index.ts",
      kit: "./src/kit/index.ts",
      annotations: "./src/annotations/index.ts",
    },
    format: ["cjs", "esm"],
    outDir: "build",
    exports: true,
    sourcemap: true,
    // Inline the Roles ABI types: the evm package is a devDependency, so an
    // import of it in the published .d.ts would not resolve for consumers.
    dts: { resolve: ["@gnosis-guild/zodiac-core-modifier-roles"] },
  },
])
