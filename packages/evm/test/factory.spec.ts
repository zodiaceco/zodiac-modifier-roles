import { expect } from "chai";
import hre, { network } from "hardhat";
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

  const paramsTypes = ["address", "address", "address"];

  async function setup() {
    const [deployer] = await ethers.getSigners();
    const Factory = await ethers.getContractFactory("ModuleProxyFactory");
    const factory = await Factory.deploy();

    const conditionStorerArtifact =
      await hre.artifacts.readArtifact("ConditionStorer");
    const ConditionStorer = new ethers.ContractFactory(
      [],
      conditionStorerArtifact.bytecode,
      deployer,
    );
    const conditionStorer = await ConditionStorer.deploy();
    const conditionStorerAddress = await conditionStorer.getAddress();

    const withinRatioCheckerArtifact =
      await hre.artifacts.readArtifact("WithinRatioChecker");
    const WithinRatioChecker = new ethers.ContractFactory(
      [],
      withinRatioCheckerArtifact.bytecode,
      deployer,
    );
    const withinRatioChecker = await WithinRatioChecker.deploy();
    const withinRatioCheckerAddress = await withinRatioChecker.getAddress();

    const customConditionCheckerArtifact = await hre.artifacts.readArtifact(
      "CustomConditionChecker",
    );
    const CustomConditionChecker = new ethers.ContractFactory(
      [],
      customConditionCheckerArtifact.bytecode,
      deployer,
    );
    const customConditionChecker = await CustomConditionChecker.deploy();
    const customConditionCheckerAddress =
      await customConditionChecker.getAddress();

    const Modifier = await ethers.getContractFactory("Roles", {
      libraries: {
        ConditionStorer: conditionStorerAddress,
        WithinRatioChecker: withinRatioCheckerAddress,
        CustomConditionChecker: customConditionCheckerAddress,
      },
    });
    const masterCopy = await Modifier.deploy(
      AddressOne,
      AddressOne,
      AddressOne,
    );
    const eip1193Provider = createEIP1193(provider, deployer);
    return { factory, masterCopy, Modifier, eip1193Provider };
  }

  it("should throw because master copy is already initialized", async () => {
    const { masterCopy } = await loadFixture(setup);
    const encodedParams = AbiCoder.defaultAbiCoder().encode(paramsTypes, [
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
    const { masterCopy, eip1193Provider } = await loadFixture(setup);
    const [avatar, owner, target] = await ethers.getSigners();
    await deployFactories({ provider: eip1193Provider });
    const { address: deployProxyAddress } = await deployProxy({
      mastercopy: await masterCopy.getAddress(),
      setupArgs: {
        types: ["address", "address", "address"],
        values: [owner.address, avatar.address, target.address],
      },
      saltNonce: ZeroHash,
      provider: eip1193Provider,
    });

    const proxy = await ethers.getContractAt("Roles", deployProxyAddress);

    expect(await proxy.avatar()).to.be.eq(avatar.address);
  });
});
