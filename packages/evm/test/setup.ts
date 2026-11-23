import { hexlify, Interface, randomBytes } from "ethers";
import type { NetworkConnection } from "hardhat/types/network";
import { deployFactories } from "@gnosis-guild/zodiac-core/tooling";

import { ExecutionOptions } from "./utils.js";
import { createEIP1193 } from "../tasks/createEIP1193.js";
import type { ConditionFlatStruct } from "../typechain-types/contracts/Roles.js";

// Side-effect imports to pull in the NetworkConnection augmentations
// (adds `ethers` and `networkHelpers` to NetworkConnection).
import "@nomicfoundation/hardhat-ethers";
import "@nomicfoundation/hardhat-network-helpers";

type InvokeOptions = { value?: bigint | number; operation?: number };

/**
 * Factory options for the contracts that link the Integrity library
 * (Evaluator, and the mocks that call it), with a freshly deployed one.
 */
export async function linkIntegrity(ethers: NetworkConnection["ethers"]) {
  const Integrity = await ethers.getContractFactory("Integrity");
  const integrity = await Integrity.deploy();
  await integrity.waitForDeployment();
  return { libraries: { Integrity: await integrity.getAddress() } };
}

export function createSetup({ ethers, provider }: NetworkConnection) {
  async function deployEvaluator() {
    const Evaluator = await ethers.getContractFactory(
      "Evaluator",
      await linkIntegrity(ethers),
    );
    const evaluator = await Evaluator.deploy();
    await evaluator.waitForDeployment();
    return evaluator;
  }

  async function deployRolesMod(
    owner: string,
    avatar: string,
    target: string,
    evaluatorAddress?: string,
  ) {
    const [signer] = await ethers.getSigners();
    await deployFactories({ provider: createEIP1193(provider, signer) });

    const evaluator =
      evaluatorAddress ?? (await (await deployEvaluator()).getAddress());

    const Modifier = await ethers.getContractFactory("Roles");
    const modifier = await Modifier.deploy(owner, avatar, target, evaluator);
    await modifier.waitForDeployment();
    return modifier;
  }

  async function setupTestContract() {
    const [owner, member] = await ethers.getSigners();

    const Avatar = await ethers.getContractFactory("TestAvatar");
    const avatar = await Avatar.deploy();

    const TestContract = await ethers.getContractFactory("TestContract");
    const testContract = await TestContract.deploy();

    const avatarAddress = await avatar.getAddress();
    const evaluator = await deployEvaluator();
    const roles = await deployRolesMod(
      owner.address,
      avatarAddress,
      avatarAddress,
      await evaluator.getAddress(),
    );

    const testContractAddress = await testContract.getAddress();
    const roleKey = hexlify(randomBytes(32));

    await roles.connect(owner).grantRole(member.address, roleKey, 0, 0, 0);
    await roles.connect(owner).setDefaultRole(member.address, roleKey);
    await roles.connect(owner).scopeTarget(roleKey, testContractAddress);

    const allowTarget = (
      conditions: ConditionFlatStruct[],
      options = ExecutionOptions.None,
    ) =>
      roles
        .connect(owner)
        .allowTarget(roleKey, testContractAddress, conditions, options);

    return {
      roles: roles.connect(owner),
      evaluator,
      owner,
      member,
      testContract,
      testContractAddress,
      roleKey,
      allowTarget,
    };
  }

  function setupFn(signature: string) {
    const iface = new Interface([signature]);
    const fn = iface.getFunction("fn")!;
    const arity = fn.inputs.length;

    return async function fixture() {
      const base = await setupTestContract();
      const { roles, member, testContractAddress, roleKey } = base;

      const allowFunction = (
        conditions: ConditionFlatStruct[],
        options = ExecutionOptions.None,
      ) =>
        roles.allowFunction(
          roleKey,
          testContractAddress,
          fn.selector,
          conditions,
          options,
        );

      const invoke = (...args: unknown[]) => {
        const options =
          args.length > arity ? (args[arity] as InvokeOptions) : undefined;
        return roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            options?.value ?? 0,
            iface.encodeFunctionData(fn, args.slice(0, arity)),
            options?.operation ?? 0,
          );
      };

      return { ...base, fn, allowFunction, invoke };
    };
  }

  return {
    deployEvaluator,
    deployRolesMod,
    setupTestContract,
    setupFn,
  };
}
