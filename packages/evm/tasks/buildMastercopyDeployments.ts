import type { HardhatRuntimeEnvironment } from "hardhat/types/hre";
import type { NetworkConnection } from "hardhat/types/network";
import { ZeroHash } from "ethers";
import { predictSingletonAddress } from "@gnosis-guild/zodiac-core";

import "@nomicfoundation/hardhat-ethers";

const AddressOne = "0x0000000000000000000000000000000000000001";

type ConstructorArgs = {
  types: string[];
  values: string[];
};

export type MastercopyDeployment = {
  address: string;
  bytecode: string;
  constructorArgs: ConstructorArgs;
  contract: string;
  contractName: string;
  libraries?: Record<string, string>;
  salt: string;
};

export async function buildMastercopyDeployments(
  hre: HardhatRuntimeEnvironment,
  connection: NetworkConnection,
): Promise<MastercopyDeployment[]> {
  const conditionStorer = await readArtifact({
    hre,
    contractName: "ConditionStorer",
    contract: "contracts/core/serialize/ConditionStorer.sol:ConditionStorer",
  });
  const withinRatioChecker = await readArtifact({
    hre,
    contractName: "WithinRatioChecker",
    contract:
      "contracts/core/evaluate/WithinRatioChecker.sol:WithinRatioChecker",
  });
  const customConditionChecker = await readArtifact({
    hre,
    contractName: "CustomConditionChecker",
    contract:
      "contracts/core/evaluate/CustomConditionChecker.sol:CustomConditionChecker",
  });
  const avatarIsOwnerOfERC721 = await readArtifact({
    hre,
    contractName: "AvatarIsOwnerOfERC721",
    contract:
      "contracts/periphery/AvatarIsOwnerOfERC721.sol:AvatarIsOwnerOfERC721",
  });
  const multiSendUnwrapper = await readArtifact({
    hre,
    contractName: "MultiSendUnwrapper",
    contract:
      "contracts/periphery/unwrappers/MultiSendUnwrapper.sol:MultiSendUnwrapper",
  });
  const signTypedMessageLib = await readArtifact({
    hre,
    contractName: "SignTypedMessageLib",
    contract:
      "contracts/periphery/signing/SignTypedMessageLib.sol:SignTypedMessageLib",
  });

  const libraries = {
    ConditionStorer: conditionStorer.address,
    WithinRatioChecker: withinRatioChecker.address,
    CustomConditionChecker: customConditionChecker.address,
  };
  const rolesFactory = await connection.ethers.getContractFactory("Roles", {
    libraries,
  });
  const roles = buildDeployment({
    contractName: "Roles",
    contract: "contracts/Roles.sol:Roles",
    bytecode: rolesFactory.bytecode,
    constructorArgs: {
      types: ["address", "address", "address"],
      values: [AddressOne, AddressOne, AddressOne],
    },
    libraries,
  });

  return [
    conditionStorer,
    withinRatioChecker,
    customConditionChecker,
    avatarIsOwnerOfERC721,
    multiSendUnwrapper,
    signTypedMessageLib,
    roles,
  ];
}

async function readArtifact({
  hre,
  contractName,
  contract,
}: {
  hre: HardhatRuntimeEnvironment;
  contractName: string;
  contract: string;
}) {
  const artifact = await hre.artifacts.readArtifact(contract);
  return buildDeployment({
    contractName,
    contract,
    bytecode: artifact.bytecode,
    constructorArgs: { types: [], values: [] },
  });
}

function buildDeployment({
  contractName,
  contract,
  bytecode,
  constructorArgs,
  libraries,
}: Omit<MastercopyDeployment, "address" | "salt">): MastercopyDeployment {
  const salt = ZeroHash;
  return {
    address: predictSingletonAddress({ bytecode, constructorArgs, salt }),
    bytecode,
    constructorArgs,
    contract,
    contractName,
    libraries,
    salt,
  };
}
