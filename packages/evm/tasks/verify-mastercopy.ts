import { readFile } from "node:fs/promises";

import { task } from "hardhat/config";
import type { HardhatRuntimeEnvironment } from "hardhat/types/hre";
import { verifyMastercopy } from "@gnosis-guild/zodiac-core/tooling";

import {
  buildMastercopyDeployments,
  type MastercopyDeployment,
} from "./buildMastercopyDeployments.js";

export default task(
  "verify:mastercopy",
  "Verifies the current Roles release (primary mastercopy plus prerequisite singleton libraries and periphery contracts) without local metadata",
)
  .setInlineAction(async (_, hre) => {
    const apiKey = process.env.ETHERSCAN_API_KEY;
    if (!apiKey) throw new Error("ETHERSCAN_API_KEY is not set");

    const connection = await hre.network.create();
    const chainId = Number(
      await connection.provider.request({ method: "eth_chainId" }),
    );

    for (const deployment of await buildMastercopyDeployments(hre)) {
      const { noop } = await verifyMastercopy({
        chainId,
        apiKey,
        artifact: await buildVerificationArtifact(hre, deployment),
      });

      console.log(
        noop
          ? `${deployment.contractName} already verified at ${deployment.address}`
          : `${deployment.contractName} verified at ${deployment.address}`,
      );
    }
  })
  .build();

type SourceUnit = {
  ast: { nodes: { nodeType: string; absolutePath?: string }[] };
};

/**
 * The contract as the explorer needs it: the compiler input of the build the
 * deployment's bytecode comes from, cut down to the sources the contract
 * imports, with the addresses of its linked libraries.
 */
export async function buildVerificationArtifact(
  hre: HardhatRuntimeEnvironment,
  deployment: MastercopyDeployment,
) {
  const { inputSourceName, linkReferences } = await hre.artifacts.readArtifact(
    deployment.contract,
  );
  const buildInfoId = await hre.artifacts.getBuildInfoId(deployment.contract);
  const inputPath = buildInfoId
    ? await hre.artifacts.getBuildInfoPath(buildInfoId)
    : undefined;
  const outputPath = buildInfoId
    ? await hre.artifacts.getBuildInfoOutputPath(buildInfoId)
    : undefined;
  if (!inputSourceName || !inputPath || !outputPath) {
    throw new Error(`No build info for ${deployment.contract}`);
  }

  const { solcLongVersion, input } = JSON.parse(
    await readFile(inputPath, "utf8"),
  );
  const { output } = JSON.parse(await readFile(outputPath, "utf8"));

  const sources: Record<string, unknown> = {};
  const pending = [inputSourceName];
  while (pending.length > 0) {
    const sourceName = pending.pop()!;
    if (sourceName in sources) continue;
    sources[sourceName] = input.sources[sourceName];
    for (const node of (output.sources[sourceName] as SourceUnit).ast.nodes) {
      if (node.nodeType === "ImportDirective") pending.push(node.absolutePath!);
    }
  }

  const libraries: Record<string, Record<string, string>> = {};
  for (const [sourceName, names] of Object.entries(linkReferences)) {
    libraries[sourceName] = {};
    for (const name of Object.keys(names)) {
      const address = deployment.libraries?.[name];
      if (!address) {
        throw new Error(
          `${deployment.contractName} links ${name}, which has no address`,
        );
      }
      libraries[sourceName][name] = address;
    }
  }

  return {
    contractName: deployment.contractName,
    sourceName: inputSourceName,
    compilerVersion: `v${solcLongVersion}`,
    compilerInput: {
      ...input,
      sources,
      settings: { ...input.settings, libraries },
    },
    address: deployment.address,
    constructorArgs: deployment.constructorArgs,
  };
}
