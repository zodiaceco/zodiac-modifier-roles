import { task } from "hardhat/config";
import {
  deployFactories,
  deployMastercopy,
} from "@gnosis-guild/zodiac-core/tooling";

import {
  buildMastercopyDeployments,
  type MastercopyDeployment,
} from "./buildMastercopyDeployments.js";
import { createEIP1193 } from "./createEIP1193.js";

export default task(
  "deploy:mastercopy",
  "Deploys the current Roles release (primary mastercopy plus prerequisite singleton libraries and periphery contracts) without persisting metadata",
)
  .setInlineAction(async (_, hre) => {
    const connection = await hre.network.create();
    const [signer] = await connection.ethers.getSigners();
    const provider = createEIP1193(connection.provider, signer);

    await deployFactories({ provider });

    for (const deployment of await buildMastercopyDeployments(
      hre,
      connection,
    )) {
      await deployOne(deployment, provider);
    }
  })
  .build();

async function deployOne(
  deployment: MastercopyDeployment,
  provider: Parameters<typeof deployMastercopy>[0]["provider"],
) {
  const { address, noop } = await deployMastercopy({
    bytecode: deployment.bytecode,
    constructorArgs: deployment.constructorArgs,
    salt: deployment.salt,
    provider,
    onStart: () => {
      console.log(`Deploying ${deployment.contractName}...`);
    },
  });

  console.log(
    noop
      ? `${deployment.contractName} already deployed at ${address}`
      : `${deployment.contractName} deployed at ${address}`,
  );
}
