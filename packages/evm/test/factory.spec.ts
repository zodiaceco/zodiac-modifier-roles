import { expect } from "chai";
import { network } from "hardhat";
import { AbiCoder, ZeroHash } from "ethers";
import {
  deployFactories,
  deployProxy,
} from "@gnosis-guild/zodiac-core/tooling";

import { createEIP1193 } from "../tasks/createEIP1193.js";

const connection = await network.create();
const { ethers, networkHelpers, provider } = connection;
const { loadFixture } = networkHelpers;

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

  const paramsTypes = ["address", "address", "address", "address"];

  async function setup() {
    const [deployer] = await ethers.getSigners();

    const Evaluator = await ethers.getContractFactory("Evaluator");
    const evaluator = await Evaluator.deploy();
    const evaluatorAddress = await evaluator.getAddress();

    const Modifier = await ethers.getContractFactory("Roles");
    const masterCopy = await Modifier.deploy(
      AddressOne,
      AddressOne,
      AddressOne,
      AddressOne,
    );
    const eip1193Provider = createEIP1193(provider, deployer);
    return { masterCopy, evaluatorAddress, eip1193Provider };
  }

  it("should throw because master copy is already initialized", async () => {
    const { masterCopy } = await loadFixture(setup);
    const encodedParams = AbiCoder.defaultAbiCoder().encode(paramsTypes, [
      AddressOne,
      AddressOne,
      AddressOne,
      AddressOne,
    ]);

    await expect(masterCopy.setUp(encodedParams)).to.be.revertedWithCustomError(
      masterCopy,
      "AlreadyInitialized",
    );
  });

  it("should deploy new roles module proxy", async () => {
    const { masterCopy, evaluatorAddress, eip1193Provider } =
      await loadFixture(setup);
    const [avatar, owner, target] = await ethers.getSigners();
    await deployFactories({ provider: eip1193Provider });
    const { address: deployProxyAddress } = await deployProxy({
      mastercopy: await masterCopy.getAddress(),
      setupArgs: {
        types: ["address", "address", "address", "address"],
        values: [
          owner.address,
          avatar.address,
          target.address,
          evaluatorAddress,
        ],
      },
      saltNonce: ZeroHash,
      provider: eip1193Provider,
    });

    const proxy = await ethers.getContractAt("Roles", deployProxyAddress);

    expect(await proxy.avatar()).to.be.eq(avatar.address);
    expect(await proxy.evaluator()).to.be.eq(evaluatorAddress);
  });
});
