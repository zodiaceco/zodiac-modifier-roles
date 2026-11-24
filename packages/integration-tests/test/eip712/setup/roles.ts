import { randomBytes } from "node:crypto"
import {
  type Address,
  type Hex,
  type PublicClient,
  type WalletClient,
  encodeAbiParameters,
  encodeFunctionData,
  toHex,
} from "viem"
import type { Condition, ExecutionOptions } from "zodiac-roles-sdk"

import { moduleProxyFactory } from "./deploy-mastercopies/moduleProxyFactory.js"
import { rolesModMastercopy } from "./deploy-mastercopies/rolesMastercopy.js"
import { enableModuleInSafe } from "./safe.js"
import type { ConditionFlat } from "../../../../evm/test/utils.js"

export async function deployRoles(
  {
    avatar,
    target,
    owner,
  }: {
    avatar: Address
    target: Address
    owner: Address
  },
  relayer: WalletClient,
  publicClient: PublicClient
) {
  function encodeSetUp() {
    const initializer = encodeAbiParameters(
      [{ type: "address" }, { type: "address" }, { type: "address" }],
      [owner, avatar, target]
    )

    return encodeFunctionData({
      abi: rolesModMastercopy.abi,
      functionName: "setUp",
      args: [initializer],
    })
  }

  const { result: address, request } = await publicClient.simulateContract({
    address: moduleProxyFactory.address,
    abi: moduleProxyFactory.abi,
    functionName: "deployModule",
    args: [rolesModMastercopy.address, encodeSetUp(), BigInt(randomHash())],
    account: relayer.account!,
  })

  await relayer.writeContract(request)

  return address
}

export async function connectRolesSafeAndMember({
  owner,
  safe,
  roles,
  member,
}: {
  owner: WalletClient
  safe: Address
  roles: Address
  member: Address
}) {
  const roleKey = randomHash()
  await enableModuleInSafe({ safe, module: roles }, owner)

  await owner.sendTransaction({
    account: owner.account!,
    chain: owner.chain,
    to: roles,
    data: encodeFunctionData({
      abi: rolesModMastercopy.abi,
      functionName: "enableModule",
      args: [member],
    }),
  })

  await owner.sendTransaction({
    account: owner.account!,
    chain: owner.chain,
    to: roles,
    data: encodeFunctionData({
      abi: rolesModMastercopy.abi,
      functionName: "assignRoles",
      args: [member, [roleKey], [true]],
    }),
  })

  return { roleKey }
}

export async function scopeTarget({
  owner,
  roles,
  roleKey,
  target,
}: {
  owner: WalletClient
  roles: Address
  roleKey: Hex
  target: Address
}) {
  await owner.sendTransaction({
    account: owner.account!,
    chain: owner.chain,
    to: roles,
    data: encodeFunctionData({
      abi: rolesModMastercopy.abi,
      functionName: "scopeTarget",
      args: [roleKey, target],
    }),
  })
}

export async function scopeFunction({
  owner,
  roles,
  roleKey,
  target,
  selector,
  condition,
  executionOptions,
}: {
  owner: WalletClient
  roles: Address
  roleKey: Hex
  target: Address
  selector: Hex
  condition: Condition
  executionOptions: ExecutionOptions
}) {
  await owner.sendTransaction({
    account: owner.account!,
    chain: owner.chain,
    to: roles,
    data: encodeFunctionData({
      abi: rolesModMastercopy.abi,
      functionName: "scopeFunction",
      args: [
        roleKey,
        target,
        selector,
        flattenCondition(condition).map((c) => ({
          parent: c.parent,
          paramType: c.paramType,
          operator: c.operator,
          compValue: c.compValue || "0x",
        })),
        executionOptions,
      ],
    }),
  })
}

export async function execTransactionWithRole({
  signer,
  roles,
  roleKey,
  to,
  data,
  operation,
}: {
  signer: WalletClient
  roles: Address
  roleKey: Hex
  to: Address
  data: Hex
  operation: number
}) {
  return signer.sendTransaction({
    account: signer.account!,
    chain: signer.chain,
    to: roles,
    data: encodeFunctionData({
      abi: rolesModMastercopy.abi,
      functionName: "execTransactionWithRole",
      args: [to, 0n, data, operation, roleKey, true],
    }),
  })
}

function randomHash(): Hex {
  return toHex(randomBytes(32))
}

const flattenCondition = (root: any): ConditionFlat[] => {
  const result: ConditionFlat[] = []
  const queue = [{ condition: root, parent: 0 }]

  while (queue.length > 0) {
    const {
      condition: { children, ...conditionFlat },
      parent,
    } = queue.shift()!

    result.push({ compValue: "0x", ...conditionFlat, parent })
    const index = result.length - 1

    if (children) {
      for (const child of children) {
        queue.push({ condition: child, parent: index })
      }
    }
  }

  return result
}
