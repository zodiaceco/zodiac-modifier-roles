import { hexlify, Interface, randomBytes, ZeroHash } from "ethers";

import { ExecutionOptions } from "./utils.js";
import { createEIP1193 } from "../tasks/createEIP1193.js";
import type { ConditionFlatStruct } from "../typechain-types/contracts/Roles.js";
import hre from "hardhat";
import type { NetworkConnection } from "hardhat/types/network";
import {
  deployFactories,
  deployMastercopy as zodiacDeployMastercopy,
} from "@gnosis-guild/zodiac-core/tooling";

// Side-effect imports to pull in the NetworkConnection augmentations
// (adds `ethers` and `networkHelpers` to NetworkConnection).
import "@nomicfoundation/hardhat-ethers";
import "@nomicfoundation/hardhat-network-helpers";

export function createSetup({ ethers, provider }: NetworkConnection) {
  async function deployRolesMod(owner: string, avatar: string, target: string) {
    const [signer] = await ethers.getSigners();
    const eip1193 = createEIP1193(provider, signer);

    await deployFactories({ provider: eip1193 });
    const conditionStorer = await hre.artifacts.readArtifact("ConditionStorer");
    const { address: conditionStorerAddress } = await zodiacDeployMastercopy({
      bytecode: conditionStorer.bytecode,
      constructorArgs: { types: [], values: [] },
      salt: ZeroHash,
      provider: eip1193,
    });

    const withinRatioChecker =
      await hre.artifacts.readArtifact("WithinRatioChecker");
    const { address: withinRatioCheckerAddress } = await zodiacDeployMastercopy(
      {
        bytecode: withinRatioChecker.bytecode,
        constructorArgs: { types: [], values: [] },
        salt: ZeroHash,
        provider: eip1193,
      },
    );

    const customConditionChecker = await hre.artifacts.readArtifact(
      "CustomConditionChecker",
    );
    const { address: customConditionCheckerAddress } =
      await zodiacDeployMastercopy({
        bytecode: customConditionChecker.bytecode,
        constructorArgs: { types: [], values: [] },
        salt: ZeroHash,
        provider: eip1193,
      });

    const Modifier = await ethers.getContractFactory("Roles", {
      libraries: {
        ConditionStorer: conditionStorerAddress,
        WithinRatioChecker: withinRatioCheckerAddress,
        CustomConditionChecker: customConditionCheckerAddress,
      },
    });
    const modifier = await Modifier.deploy(owner, avatar, target);
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
    const roles = await deployRolesMod(
      owner.address,
      avatarAddress,
      avatarAddress,
    );

    const testContractAddress = await testContract.getAddress();
    const roleKey = hexlify(randomBytes(32));

    await roles.connect(owner).enableModule(member.address);
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
      owner,
      member,
      testContract,
      testContractAddress,
      roleKey,
      allowTarget,
    };
  }

  async function setupOneParam() {
    const iface = new Interface(["function fn(uint256)"]);
    const fn = iface.getFunction("fn")!;
    const { owner, roles, member, testContractAddress, roleKey } =
      await setupTestContract();

    const allowFunction = async (
      conditions: ConditionFlatStruct[],
      options = ExecutionOptions.None,
    ) => {
      return roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        conditions,
        options,
      );
    };

    const invoke = (
      a: bigint | number,
      options?: { value?: bigint | number; operation?: number },
    ) =>
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          options?.value ?? 0,
          iface.encodeFunctionData(fn, [a]),
          options?.operation ?? 0,
        );

    return {
      owner,
      roles,
      member,
      testContractAddress,
      roleKey,
      fn,
      allowFunction,
      invoke,
    };
  }

  async function setupOneParamSigned() {
    const iface = new Interface(["function fn(int256)"]);
    const fn = iface.getFunction("fn")!;
    const { owner, roles, member, testContractAddress, roleKey } =
      await setupTestContract();

    const allowFunction = async (
      conditions: ConditionFlatStruct[],
      options = ExecutionOptions.None,
    ) => {
      return roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        conditions,
        options,
      );
    };

    const invoke = (
      a: bigint | number,
      options?: { value?: bigint | number; operation?: number },
    ) =>
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          options?.value ?? 0,
          iface.encodeFunctionData(fn, [a]),
          options?.operation ?? 0,
        );

    return {
      owner,
      roles,
      member,
      testContractAddress,
      roleKey,
      fn,
      allowFunction,
      invoke,
    };
  }

  async function setupTwoParams() {
    const iface = new Interface(["function fn(uint256, uint256)"]);
    const fn = iface.getFunction("fn")!;
    const { owner, roles, member, testContractAddress, roleKey } =
      await setupTestContract();

    const allowFunction = async (
      conditions: ConditionFlatStruct[],
      options = ExecutionOptions.None,
    ) => {
      return roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        conditions,
        options,
      );
    };

    const invoke = (
      a: bigint | number,
      b: bigint | number,
      options?: { value?: bigint | number; operation?: number },
    ) =>
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          options?.value ?? 0,
          iface.encodeFunctionData(fn, [a, b]),
          options?.operation ?? 0,
        );

    return {
      owner,
      roles,
      member,
      testContractAddress,
      roleKey,
      fn,
      allowFunction,
      invoke,
    };
  }

  async function setupDynamicParam() {
    const iface = new Interface(["function fn(bytes)"]);
    const fn = iface.getFunction("fn")!;
    const { owner, roles, member, testContractAddress, roleKey } =
      await setupTestContract();

    const allowFunction = async (
      conditions: ConditionFlatStruct[],
      options = ExecutionOptions.None,
    ) => {
      return roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        conditions,
        options,
      );
    };

    const invoke = (
      data: string,
      options?: { value?: bigint | number; operation?: number },
    ) =>
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          options?.value ?? 0,
          iface.encodeFunctionData(fn, [data]),
          options?.operation ?? 0,
        );

    return {
      owner,
      roles,
      member,
      testContractAddress,
      roleKey,
      fn,
      allowFunction,
      invoke,
    };
  }

  async function setupArrayParam() {
    const iface = new Interface(["function fn(uint256[])"]);
    const fn = iface.getFunction("fn")!;
    const { owner, roles, member, testContractAddress, roleKey } =
      await setupTestContract();

    const allowFunction = async (
      conditions: ConditionFlatStruct[],
      options = ExecutionOptions.None,
    ) => {
      return roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        conditions,
        options,
      );
    };

    const invoke = (
      arr: (bigint | number)[],
      options?: { value?: bigint | number; operation?: number },
    ) =>
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          options?.value ?? 0,
          iface.encodeFunctionData(fn, [arr]),
          options?.operation ?? 0,
        );

    return {
      roles,
      owner,
      member,
      testContractAddress,
      roleKey,
      fn,
      allowFunction,
      invoke,
    };
  }

  async function setupTwoArrayParams() {
    const iface = new Interface(["function fn(uint256[], uint256[])"]);
    const fn = iface.getFunction("fn")!;
    const { owner, roles, member, testContractAddress, roleKey } =
      await setupTestContract();

    const allowFunction = async (
      conditions: ConditionFlatStruct[],
      options = ExecutionOptions.None,
    ) => {
      return roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        conditions,
        options,
      );
    };

    const invoke = (
      arr1: (bigint | number)[],
      arr2: (bigint | number)[],
      options?: { value?: bigint | number; operation?: number },
    ) =>
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          options?.value ?? 0,
          iface.encodeFunctionData(fn, [arr1, arr2]),
          options?.operation ?? 0,
        );

    return {
      roles,
      owner,
      member,
      testContractAddress,
      roleKey,
      fn,
      allowFunction,
      invoke,
    };
  }

  async function setupThreeArrayParams(type = "uint256") {
    const iface = new Interface([
      `function fn(${type}[], ${type}[], ${type}[])`,
    ]);
    const fn = iface.getFunction("fn")!;
    const { owner, roles, member, testContractAddress, roleKey } =
      await setupTestContract();

    const allowFunction = async (
      conditions: ConditionFlatStruct[],
      options = ExecutionOptions.None,
    ) => {
      return roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        conditions,
        options,
      );
    };

    const invoke = (
      arr1: (bigint | number | string)[],
      arr2: (bigint | number | string)[],
      arr3: (bigint | number | string)[],
      options?: { value?: bigint | number; operation?: number },
    ) =>
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          options?.value ?? 0,
          iface.encodeFunctionData(fn, [arr1, arr2, arr3]),
          options?.operation ?? 0,
        );

    return {
      roles,
      owner,
      member,
      testContractAddress,
      roleKey,
      fn,
      allowFunction,
      invoke,
    };
  }

  async function setupTwoTupleArrayParams() {
    const iface = new Interface([
      "function fn((uint256, uint256)[], (uint256, uint256)[])",
    ]);
    const fn = iface.getFunction("fn")!;
    const { owner, roles, member, testContractAddress, roleKey } =
      await setupTestContract();

    const allowFunction = async (
      conditions: ConditionFlatStruct[],
      options = ExecutionOptions.None,
    ) => {
      return roles.allowFunction(
        roleKey,
        testContractAddress,
        fn.selector,
        conditions,
        options,
      );
    };

    const invoke = (
      arr1: [bigint | number, bigint | number][],
      arr2: [bigint | number, bigint | number][],
      options?: { value?: bigint | number; operation?: number },
    ) =>
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          options?.value ?? 0,
          iface.encodeFunctionData(fn, [arr1, arr2]),
          options?.operation ?? 0,
        );

    return {
      roles,
      owner,
      member,
      testContractAddress,
      roleKey,
      fn,
      allowFunction,
      invoke,
    };
  }

  return {
    deployRolesMod,
    setupTestContract,
    setupOneParam,
    setupOneParamSigned,
    setupTwoParams,
    setupDynamicParam,
    setupArrayParam,
    setupTwoArrayParams,
    setupThreeArrayParams,
    setupTwoTupleArrayParams,
  };
}
