/**
 * The EIP-712 `RoleTx` that `execTransactionWithRoleSigned` takes, for
 * signing and hashing in tests, and the four execution entrypoints. Depends
 * only on ethers, so the integration tests import it too.
 */
import { hexlify, randomBytes } from "ethers";
import type { BigNumberish, Interface, Signer } from "ethers";

/** A deadline that never passes: the largest uint64. */
export const NO_DEADLINE = 2n ** 64n - 1n;

export const ROLE_TX_TYPES = {
  RoleTx: [
    { name: "to", type: "address" },
    { name: "value", type: "uint256" },
    { name: "data", type: "bytes" },
    { name: "operation", type: "uint8" },
    { name: "roleKey", type: "bytes32" },
    { name: "salt", type: "bytes32" },
    { name: "deadline", type: "uint64" },
  ],
};

export type RoleTx = {
  to: string;
  value: BigNumberish;
  data: string;
  operation: number;
  roleKey: string;
  salt: string;
  deadline: BigNumberish;
};

export const ENTRYPOINTS = [
  "execTransactionFromModule",
  "execTransactionFromModuleReturnData",
  "execTransactionWithRole",
  "execTransactionWithRoleSigned",
] as const;
export type Entrypoint = (typeof ENTRYPOINTS)[number];

/**
 * Calldata for `entrypoint` on `roles`, executing `call`. The IAvatar
 * entrypoints take no role (the sender's default role applies) and only the
 * signed one takes a salt and a deadline (random and none, unless given),
 * with a signature by `signer`.
 */
export async function encodeEntrypoint(
  roles: { interface: Interface; getAddress(): Promise<string> },
  entrypoint: Entrypoint,
  call: Pick<RoleTx, "to" | "data" | "roleKey"> & Partial<RoleTx>,
  signer?: Signer,
): Promise<string> {
  const { to, value = 0, data, operation = 0, roleKey } = call;
  if (entrypoint === "execTransactionWithRoleSigned") {
    const roleTx = {
      to,
      value,
      data,
      operation,
      roleKey,
      salt: call.salt ?? hexlify(randomBytes(32)),
      deadline: call.deadline ?? NO_DEADLINE,
    };
    const domain = {
      chainId: (await signer!.provider!.getNetwork()).chainId,
      verifyingContract: await roles.getAddress(),
    };
    return roles.interface.encodeFunctionData(entrypoint, [
      roleTx,
      await signer!.signTypedData(domain, ROLE_TX_TYPES, roleTx),
    ]);
  }
  return roles.interface.encodeFunctionData(
    entrypoint,
    entrypoint === "execTransactionWithRole"
      ? [to, value, data, operation, roleKey]
      : [to, value, data, operation],
  );
}
