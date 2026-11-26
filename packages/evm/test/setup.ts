import { randomBytes } from "node:crypto";
import { encodeFunctionData, parseAbi, toFunctionSelector, toHex } from "viem";
import type { Abi, AbiFunction, Address } from "viem";
import type { NetworkConnection } from "hardhat/types/network";
import { deployFactories } from "@gnosis-guild/zodiac-core/tooling";

import {
  ExecutionOptions,
  type ConditionFlat,
  type RolesContract,
} from "./utils.js";
import type { GetContractReturnType } from "@nomicfoundation/hardhat-viem/types";
import type { ArtifactMap } from "hardhat/types/artifacts";

export type EvaluatorContract = GetContractReturnType<
  ArtifactMap["Evaluator"]["abi"]
>;
import { createEIP1193 } from "../tasks/createEIP1193.js";

// Side-effect imports to pull in the NetworkConnection augmentations
// (adds `viem` with `assertions` and `networkHelpers` to NetworkConnection).
import "@nomicfoundation/hardhat-viem";
import "@nomicfoundation/hardhat-viem-assertions";
import "@nomicfoundation/hardhat-network-helpers";

type InvokeOptions = { value?: bigint | number; operation?: number };

/**
 * Factory options for the contracts that link the Integrity library
 * (Evaluator, and the mocks that call it), with a freshly deployed one.
 */
export async function linkIntegrity(viem: NetworkConnection["viem"]) {
  const integrity = await viem.deployContract("Integrity");
  return { libraries: { Integrity: integrity.address } };
}

export function createSetup({ viem, provider }: NetworkConnection) {
  async function deployEvaluator(): Promise<EvaluatorContract> {
    return viem.deployContract("Evaluator", [], await linkIntegrity(viem));
  }

  async function deployRolesMod(
    owner: Address,
    avatar: Address,
    target: Address,
    evaluatorAddress?: Address,
  ): Promise<RolesContract> {
    const [walletClient] = await viem.getWalletClients();
    await deployFactories({ provider: createEIP1193(provider, walletClient) });

    const evaluator = evaluatorAddress ?? (await deployEvaluator()).address;
    return viem.deployContract("Roles", [owner, avatar, target, evaluator]);
  }

  /** MultiSend and its unwrapper, registered on `roles` (as its owner). */
  async function deployMultiSend(roles: RolesContract) {
    const multisend = await viem.deployContract("MultiSend");
    const unwrapper = await viem.deployContract("MultiSendUnwrapper");
    await roles.write.setTransactionUnwrapper([
      multisend.address,
      toFunctionSelector("multiSend(bytes)"),
      unwrapper.address,
    ]);
    return { multisend, unwrapper };
  }

  async function setupTestContract() {
    const [owner, member] = await viem.getWalletClients();

    const avatar = await viem.deployContract("TestAvatar");
    const testContract = await viem.deployContract("TestContract");
    const evaluator = await deployEvaluator();
    const roles = await deployRolesMod(
      owner.account.address,
      avatar.address,
      avatar.address,
      evaluator.address,
    );

    const testContractAddress = testContract.address;
    const roleKey = toHex(randomBytes(32));

    await roles.write.grantRole([member.account.address, roleKey, 0n, 0n, 0n]);
    await roles.write.setDefaultRole([member.account.address, roleKey]);
    await roles.write.scopeTarget([roleKey, testContractAddress]);

    const allowTarget = (
      conditions: ConditionFlat[],
      options = ExecutionOptions.None,
    ) =>
      roles.write.allowTarget([
        roleKey,
        testContractAddress,
        conditions,
        options,
      ]);

    return {
      roles,
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
    const abi = parseAbi([signature]) as Abi;
    const fn = abi[0] as AbiFunction;
    const selector = toFunctionSelector(fn);
    const arity = fn.inputs.length;

    return async function fixture() {
      const base = await setupTestContract();
      const { roles, member, testContractAddress, roleKey } = base;

      const allowFunction = (
        conditions: ConditionFlat[],
        options = ExecutionOptions.None,
      ) =>
        roles.write.allowFunction([
          roleKey,
          testContractAddress,
          selector,
          conditions,
          options,
        ]);

      const invoke = (...args: unknown[]) => {
        const options =
          args.length > arity ? (args[arity] as InvokeOptions) : undefined;
        return roles.write.execTransactionFromModule(
          [
            testContractAddress,
            BigInt(options?.value ?? 0),
            encodeFunctionData({
              abi: [fn],
              functionName: fn.name,
              args: args.slice(0, arity),
            }),
            options?.operation ?? 0,
          ],
          { account: member.account },
        );
      };

      return { ...base, fn, selector, allowFunction, invoke };
    };
  }

  return {
    deployEvaluator,
    deployRolesMod,
    deployMultiSend,
    setupTestContract,
    setupFn,
  };
}
