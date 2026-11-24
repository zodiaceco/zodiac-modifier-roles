/**
 * The EIP-712 `RoleTx` that `execTransactionWithRoleSigned` takes, for
 * signing and hashing in tests, and the four execution entrypoints. Depends
 * only on viem, so the integration tests import it too.
 */
import { randomBytes } from "node:crypto";
import { encodeFunctionData, toHex } from "viem";
import type { Abi, Address, Hex, WalletClient } from "viem";

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
} as const;

export type RoleTx = {
  to: Address;
  value: bigint;
  data: Hex;
  operation: number;
  roleKey: Hex;
  salt: Hex;
  deadline: bigint;
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
  roles: { abi: Abi; address: Address },
  entrypoint: Entrypoint,
  call: Pick<RoleTx, "to" | "data" | "roleKey"> &
    Partial<Omit<RoleTx, "value" | "deadline">> & {
      value?: bigint | number;
      deadline?: bigint | number;
    },
  signer?: WalletClient,
): Promise<Hex> {
  const { to, value = 0n, data, operation = 0, roleKey } = call;
  if (entrypoint === "execTransactionWithRoleSigned") {
    const roleTx: RoleTx = {
      to,
      value: BigInt(value),
      data,
      operation,
      roleKey,
      salt: call.salt ?? toHex(randomBytes(32)),
      deadline: BigInt(call.deadline ?? NO_DEADLINE),
    };
    const domain = {
      chainId: await signer!.getChainId(),
      verifyingContract: roles.address,
    };
    const signature = await signer!.signTypedData({
      account: signer!.account!,
      domain,
      types: ROLE_TX_TYPES,
      primaryType: "RoleTx",
      message: roleTx,
    });
    return encodeFunctionData({
      abi: roles.abi,
      functionName: entrypoint,
      args: [roleTx, signature],
    });
  }
  return encodeFunctionData({
    abi: roles.abi,
    functionName: entrypoint,
    args:
      entrypoint === "execTransactionWithRole"
        ? [to, BigInt(value), data, operation, roleKey]
        : [to, BigInt(value), data, operation],
  });
}
