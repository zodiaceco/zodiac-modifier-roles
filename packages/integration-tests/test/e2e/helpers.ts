/**
 * What the end-to-end specs share: deploying Roles on a Safe, executing as
 * the Safe's owner, MultiSend batches, the condition enums they use and a
 * seeded PRNG.
 */
import { randomBytes } from "node:crypto"
import {
  type Address,
  type Hex,
  type WalletClient,
  concat,
  encodeAbiParameters,
  encodeFunctionData,
  parseAbi,
  toFunctionSelector,
  toHex,
  zeroAddress,
  zeroHash,
} from "viem"
import type { NetworkConnection } from "hardhat/types/network"
import "@nomicfoundation/hardhat-viem"

import { safeAbi as abiSafe } from "../eip712/setup/safe-deployments/index.js"
import { deploySafe } from "../eip712/setup/safe.js"

import {
  type RolesContract,
  encodeMultisendPayload,
} from "../../../evm/test/utils.js"

export { NO_DEADLINE, ROLE_TX_TYPES } from "../../../evm/test/roleTx.js"
export type { RoleTx } from "../../../evm/test/roleTx.js"

export const multiSendAbi = parseAbi(["function multiSend(bytes transactions)"])

/** The members of Roles' enums that these specs write conditions with. */
export const Encoding = { EtherValue: 6 } as const
export const Operator = { WithinAllowance: 28 } as const
export const ExecutionOptions = {
  None: 0,
  Send: 1,
  DelegateCall: 2,
  Both: 3,
} as const

export const randomKey = (): Hex => toHex(randomBytes(32))

/** Roles, with its own Evaluator, avatar and target `avatar`. */
export async function deployRoles(
  viem: NetworkConnection["viem"],
  owner: Address,
  avatar: Address
): Promise<RolesContract> {
  const integrity = await viem.deployContract("Integrity")
  const evaluator = await viem.deployContract("Evaluator", [], {
    libraries: { Integrity: integrity.address },
  })
  return viem.deployContract("Roles", [
    owner,
    avatar,
    avatar,
    evaluator.address,
  ])
}

/** `owner` (threshold 1) executes a call from the Safe, and returns its tx hash. */
export async function execSafe(
  owner: WalletClient,
  safe: Address,
  to: Address,
  data: Hex,
  operation = 0,
  value = 0n
) {
  const approval = concat([
    encodeAbiParameters([{ type: "address" }], [owner.account!.address]),
    zeroHash,
    "0x01",
  ])
  return owner.sendTransaction({
    account: owner.account!,
    chain: owner.chain,
    to: safe,
    data: encodeFunctionData({
      abi: abiSafe,
      functionName: "execTransaction",
      args: [
        to,
        value,
        data,
        operation,
        0n,
        0n,
        0n,
        zeroAddress,
        zeroAddress,
        approval,
      ],
    }),
  })
}

/** A Safe owned by `owner` with a Roles Modifier enabled as its module. */
export async function safeWithRoles(
  viem: NetworkConnection["viem"],
  owner: WalletClient
) {
  const safe = await deploySafe(
    {
      owners: [owner.account!.address],
      threshold: 1,
      creationNonce: BigInt(randomKey()),
    },
    owner
  )
  const roles = await deployRoles(viem, owner.account!.address, safe)
  await execSafe(
    owner,
    safe,
    safe,
    encodeFunctionData({
      abi: abiSafe,
      functionName: "enableModule",
      args: [roles.address],
    })
  )
  return { safe, roles }
}

/** MultiSend, with its unwrapper registered on `roles` (connected to its
 *  owner). Returns MultiSend's address. */
export async function deployMultiSend(
  viem: NetworkConnection["viem"],
  roles: RolesContract,
  owner?: WalletClient
): Promise<Address> {
  const multiSend = await viem.deployContract("MultiSend")
  const unwrapper = await viem.deployContract("MultiSendUnwrapper")
  await roles.write.setTransactionUnwrapper(
    [
      multiSend.address,
      toFunctionSelector("multiSend(bytes)"),
      unwrapper.address,
    ],
    owner ? { account: owner.account } : undefined
  )
  return multiSend.address
}

export type MultiSendTx = {
  to: Address
  value: bigint
  data?: Hex
  operation?: number
}

/** MultiSend's packed transactions: operation, to, value, length, data. */
export const packMultiSend = (txs: MultiSendTx[]) =>
  encodeMultisendPayload(
    txs.map(({ to, value, data = "0x", operation = 0 }) => ({
      to,
      value,
      data,
      operation,
    }))
  )

export const encodeMultiSend = (txs: MultiSendTx[]) =>
  encodeFunctionData({
    abi: multiSendAbi,
    functionName: "multiSend",
    args: [packMultiSend(txs)],
  })

/** A seeded PRNG (an LCG), so a failing fuzz run is replayed by its seed. */
export function prng(seed: number) {
  let state = seed
  const rnd = () => {
    state = (state * 1103515245 + 12345) % 2 ** 31
    return state / 2 ** 31
  }
  const int = (n: number) => Math.floor(rnd() * n)
  return {
    seed,
    rnd,
    int,
    pick: <T>(xs: readonly T[]): T => xs[int(xs.length)],
    chance: (p: number) => rnd() < p,
  }
}

export const count = (t: Record<string, number>, k: string) => {
  t[k] = (t[k] ?? 0) + 1
}
