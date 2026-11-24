import assert from "node:assert/strict";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import { encodeAbiParameters, getAddress, zeroHash } from "viem";
import {
  deployFactories,
  deployProxy,
} from "@gnosis-guild/zodiac-core/tooling";

import { createEIP1193 } from "../tasks/createEIP1193.js";
import { createSetup } from "./setup.js";

const connection = await network.create();
const { viem, networkHelpers, provider } = connection;
const { loadFixture } = networkHelpers;
const { deployEvaluator } = createSetup(connection);

const AddressOne = "0x0000000000000000000000000000000000000001";

/**
 * Factory tests
 *
 * Scope: Module Deployment & Initialization.
 *
 * This file verifies the deployment process via the ModuleProxyFactory:
 * - Master Copy Safety: Ensuring the master copy is initialized and cannot be taken over.
 * - Proxy Deployment: Verifying that new module proxies are correctly deployed and initialized with the specified parameters.
 */

describe("Module works with factory", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [deployer] = await viem.getWalletClients();

    const evaluator = await deployEvaluator();
    const evaluatorAddress = evaluator.address;

    const masterCopy = await viem.deployContract("Roles", [
      AddressOne,
      AddressOne,
      AddressOne,
      AddressOne,
    ]);
    const eip1193Provider = createEIP1193(provider, deployer);
    return { masterCopy, evaluatorAddress, eip1193Provider };
  }

  it("should throw because master copy is already initialized", async () => {
    const { masterCopy } = await loadFixture(setup);
    const encodedParams = encodeAbiParameters(
      [
        { type: "address" },
        { type: "address" },
        { type: "address" },
        { type: "address" },
      ],
      [AddressOne, AddressOne, AddressOne, AddressOne],
    );

    await viem.assertions.revertWithCustomError(
      masterCopy.write.setUp([encodedParams]),
      masterCopy,
      "AlreadyInitialized",
    );
  });

  it("should deploy new roles module proxy", async () => {
    const { masterCopy, evaluatorAddress, eip1193Provider } =
      await loadFixture(setup);
    const [avatar, owner, target] = await viem.getWalletClients();
    await deployFactories({ provider: eip1193Provider });
    const { address: deployProxyAddress } = await deployProxy({
      mastercopy: masterCopy.address,
      setupArgs: {
        types: ["address", "address", "address", "address"],
        values: [
          owner.account.address,
          avatar.account.address,
          target.account.address,
          evaluatorAddress,
        ],
      },
      saltNonce: zeroHash,
      provider: eip1193Provider,
    });

    const proxy = await viem.getContractAt(
      "Roles",
      getAddress(deployProxyAddress),
    );

    assert.equal(
      getAddress(await proxy.read.avatar()),
      getAddress(avatar.account.address),
    );
    assert.equal(
      getAddress(await proxy.read.evaluator()),
      getAddress(evaluatorAddress),
    );
  });
});
