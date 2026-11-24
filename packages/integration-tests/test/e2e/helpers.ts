/**
 * What the end-to-end specs share: deploying Roles on a Safe, executing as
 * the Safe's owner, MultiSend batches, the condition enums they use and a
 * seeded PRNG.
 */
import {
  AbiCoder,
  Interface,
  ZeroAddress,
  ZeroHash,
  concat,
  hexlify,
  randomBytes,
} from "ethers"
import type { Signer } from "ethers"
import type { HardhatEthers } from "@nomicfoundation/hardhat-ethers/types"

import { iface as ifaceSafe } from "../eip712/setup/deploy-mastercopies/safeMastercopy.js"
import { deploySafe } from "../eip712/setup/safe.js"

import { encodeMultisendPayload } from "../../../evm/test/utils.js"

export { NO_DEADLINE, ROLE_TX_TYPES } from "../../../evm/test/roleTx.js"
export type { RoleTx } from "../../../evm/test/roleTx.js"

const abi = AbiCoder.defaultAbiCoder()

export const multiSendIface = new Interface([
  "function multiSend(bytes transactions)",
])

/** The members of Roles' enums that these specs write conditions with. */
export const Encoding = { EtherValue: 6 } as const
export const Operator = { WithinAllowance: 28 } as const
export const ExecutionOptions = {
  None: 0,
  Send: 1,
  DelegateCall: 2,
  Both: 3,
} as const

export const randomKey = () => hexlify(randomBytes(32))

/** Roles, with its own Evaluator, avatar and target `avatar`. */
export async function deployRoles(
  ethers: HardhatEthers,
  owner: string,
  avatar: string
) {
  const integrity = await (
    await ethers.getContractFactory("Integrity")
  ).deploy()
  const evaluator = await (
    await ethers.getContractFactory("Evaluator", {
      libraries: { Integrity: await integrity.getAddress() },
    })
  ).deploy()
  return (await ethers.getContractFactory("Roles")).deploy(
    owner,
    avatar,
    avatar,
    await evaluator.getAddress()
  )
}

/** `owner` (threshold 1) executes a call from the Safe, and waits for it. */
export async function execSafe(
  owner: Signer,
  safe: string,
  to: string,
  data: string,
  operation = 0,
  value = 0n
) {
  const approval = concat([
    abi.encode(["address"], [await owner.getAddress()]),
    ZeroHash,
    "0x01",
  ])
  const tx = await owner.sendTransaction({
    to: safe,
    data: ifaceSafe.encodeFunctionData("execTransaction", [
      to,
      value,
      data,
      operation,
      0n,
      0n,
      0n,
      ZeroAddress,
      ZeroAddress,
      approval,
    ]),
  })
  return tx.wait()
}

/** A Safe owned by `owner` with a Roles Modifier enabled as its module. */
export async function safeWithRoles(ethers: HardhatEthers, owner: Signer) {
  const safe = await deploySafe(
    {
      owners: [await owner.getAddress()],
      threshold: 1,
      creationNonce: BigInt(randomKey()),
    },
    owner as any
  )
  const roles = await deployRoles(ethers, await owner.getAddress(), safe)
  await execSafe(
    owner,
    safe,
    safe,
    ifaceSafe.encodeFunctionData("enableModule", [await roles.getAddress()])
  )
  return { safe, roles }
}

/** MultiSend, with its unwrapper registered on `roles` (connected to its
 *  owner). Returns MultiSend's address. */
export async function deployMultiSend(ethers: HardhatEthers, roles: any) {
  const multiSend = await (
    await ethers.getContractFactory("MultiSend")
  ).deploy()
  const unwrapper = await (
    await ethers.getContractFactory("MultiSendUnwrapper")
  ).deploy()
  await roles.setTransactionUnwrapper(
    await multiSend.getAddress(),
    multiSendIface.getFunction("multiSend")!.selector,
    await unwrapper.getAddress()
  )
  return multiSend.getAddress()
}

export type MultiSendTx = {
  to: string
  value: bigint
  data?: string
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
  multiSendIface.encodeFunctionData("multiSend", [packMultiSend(txs)])

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
