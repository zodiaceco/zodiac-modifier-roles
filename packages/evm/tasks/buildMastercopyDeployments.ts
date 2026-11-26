import type { HardhatRuntimeEnvironment } from "hardhat/types/hre";
import type { LinkReferences } from "hardhat/types/artifacts";
import { getAddress, zeroHash } from "viem";
import { predictSingletonAddress } from "@gnosis-guild/zodiac-core";

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

export function linkBytecode(
  bytecode: string,
  linkReferences: LinkReferences,
  libraries: Record<string, string>,
): string {
  let linked = bytecode;
  for (const names of Object.values(linkReferences)) {
    for (const [name, refs] of Object.entries(names)) {
      const address = libraries[name];
      if (!address) {
        throw new Error(`Missing library address for ${name}`);
      }
      const hexAddress = getAddress(address).slice(2).toLowerCase();
      for (const { start, length } of refs) {
        const offset = 2 + start * 2;
        const hexLen = length * 2;
        if (hexAddress.length !== hexLen) {
          throw new Error(
            `Unexpected link reference length ${length} for ${name}`,
          );
        }
        linked =
          linked.slice(0, offset) + hexAddress + linked.slice(offset + hexLen);
      }
    }
  }
  return linked;
}

export async function buildMastercopyDeployments(
  hre: HardhatRuntimeEnvironment,
): Promise<MastercopyDeployment[]> {
  const integrity = await readArtifact({
    hre,
    contractName: "Integrity",
    contract: "contracts/evaluator/Integrity.sol:Integrity",
  });
  // Evaluator links Integrity: its bytecode, and so its address, depend on
  // where Integrity is deployed.
  const evaluatorLibraries = { Integrity: integrity.address };
  const evaluatorArtifact = await hre.artifacts.readArtifact(
    "contracts/evaluator/Evaluator.sol:Evaluator",
  );
  const evaluator = buildDeployment({
    contractName: "Evaluator",
    contract: "contracts/evaluator/Evaluator.sol:Evaluator",
    bytecode: linkBytecode(
      evaluatorArtifact.bytecode,
      evaluatorArtifact.linkReferences,
      evaluatorLibraries,
    ),
    constructorArgs: { types: [], values: [] },
    libraries: evaluatorLibraries,
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

  const rolesArtifact = await hre.artifacts.readArtifact(
    "contracts/Roles.sol:Roles",
  );
  const roles = buildDeployment({
    contractName: "Roles",
    contract: "contracts/Roles.sol:Roles",
    bytecode: rolesArtifact.bytecode,
    constructorArgs: {
      types: ["address", "address", "address", "address"],
      values: [AddressOne, AddressOne, AddressOne, AddressOne],
    },
  });

  // In deployment order: a library before the contract that links it.
  return [
    integrity,
    evaluator,
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
  const salt = zeroHash;
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
