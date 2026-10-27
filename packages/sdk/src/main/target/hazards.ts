import {
  Clearance,
  Condition,
  Encoding,
  ExecutionOptions,
  Operator,
  Target,
} from "../types"
import { AbiCoder, id } from "ethers"

import { SIGN_TYPED_MESSAGE_LIB_ADDRESS } from "../addresses"

export interface PermissionHazard {
  target: `0x${string}`
  selector?: `0x${string}`
  kind:
    | "delegatecall-target"
    | "delegatecall-function"
    | "sign-message"
    | "sign-typed-message-types"
    | "sign-typed-message-domain"
    | "sign-typed-message-authority"
    | "roles-modifier"
  message: string
}

const SIGN_MESSAGE = "0x85a5affe" // signMessage(bytes)
const PERSONAL_SIGN = "0x641e3d2b" // personalSign(bytes)

const allowsDelegateCall = (o: ExecutionOptions) =>
  o === ExecutionOptions.DelegateCall || o === ExecutionOptions.Both

const same = (a: string, b: string) => a.toLowerCase() === b.toLowerCase()

/**
 * Permissions that grant more than they appear to. These are not invalid
 * (the contract accepts them, and a few setups intend them), so this returns
 * warnings instead of throwing:
 *
 * - `delegatecall-target`: delegatecall to any function of a target. The
 *   target's code runs in the avatar and can change any of its storage
 *   (owners, modules, signed messages).
 * - `delegatecall-function`: delegatecall to a function of a target other
 *   than the signing library. Trust the target's code like the avatar's own.
 * - `sign-message`: `SignTypedMessageLib.signMessage` without pinning exact
 *   messages. It signs a raw hash, and a signature of the avatar is accepted
 *   wherever its EIP-1271 signature counts: other Roles Modifiers where it is
 *   a member, Safes it owns, any app. A condition on a hash cannot tell what
 *   was hashed.
 * - `sign-typed-message-types`: a typed-message selector of the signing
 *   library whose condition does not pin `types`. The library accepts typed
 *   messages under any selector, so this allows any typed message.
 * - `sign-typed-message-domain`: a typed-message permission that does not
 *   pin the domain's `chainId` and `verifyingContract` (or whose domain lacks
 *   either field, or has an unknown layout), so the role can sign that
 *   message type for other contracts or chains.
 * - `sign-typed-message-authority`: typed messages that authorize actions
 *   of the avatar elsewhere: `RoleTx` (relayed transactions of a Roles
 *   Modifier where the avatar is a member), `SafeTx` and `SafeMessage`
 *   (transactions and messages of Safes the avatar owns).
 * - `roles-modifier`: calls to the Roles Modifier itself. Through the avatar
 *   (its owner) this is configuration access, and settlement of the same
 *   transaction overwrites allowance and membership changes it makes.
 *
 * @param targets The role's targets (`processPermissions(...).targets`)
 * @param options.signingLib Address of `SignTypedMessageLib`
 * @param options.rolesModifier Address of the Roles Modifier the role is on
 */
export const permissionHazards = (
  targets: readonly Target[],
  {
    signingLib = SIGN_TYPED_MESSAGE_LIB_ADDRESS,
    rolesModifier,
  }: { signingLib?: string; rolesModifier?: string } = {}
): PermissionHazard[] => {
  const hazards: PermissionHazard[] = []

  for (const target of targets) {
    const { address } = target
    const isSigningLib = same(address, signingLib)

    if (rolesModifier && same(address, rolesModifier)) {
      hazards.push({
        target: address,
        kind: "roles-modifier",
        message: `${address} is the Roles Modifier itself: through the avatar this is configuration access, and settlement of the same transaction overwrites the allowance and membership changes it makes`,
      })
    }

    if (
      target.clearance === Clearance.Target &&
      allowsDelegateCall(target.executionOptions)
    ) {
      hazards.push({
        target: address,
        kind: "delegatecall-target",
        message: `delegatecall to any function of ${address}: its code runs in the avatar and can change any of its storage${isSigningLib ? ", and the signing library signs anything" : ""}`,
      })
    }

    if (target.clearance !== Clearance.Function) continue

    for (const fn of target.functions) {
      if (!allowsDelegateCall(fn.executionOptions)) continue
      const { selector } = fn
      const at = { target: address, selector }

      if (!isSigningLib) {
        hazards.push({
          ...at,
          kind: "delegatecall-function",
          message: `delegatecall to ${address} (${selector}): its code runs in the avatar, trust it like the avatar's own`,
        })
        continue
      }

      if (same(selector, PERSONAL_SIGN)) continue

      if (same(selector, SIGN_MESSAGE)) {
        if (
          !fn.condition ||
          !pinsParameter(fn.condition, 0, Encoding.Dynamic)
        ) {
          hazards.push({
            ...at,
            kind: "sign-message",
            message:
              "signMessage signs a raw hash: unless exact messages are pinned, the role can make the avatar sign anything, including transactions of other Roles Modifiers and Safes that accept its signature",
          })
        }
        continue
      }

      // any other selector is signTypedMessage (the library's fallback)
      if (!fn.condition || !pinsParameter(fn.condition, 2, Encoding.Array)) {
        hazards.push({
          ...at,
          kind: "sign-typed-message-types",
          message:
            "the signing library accepts typed messages under any selector: without pinning `types`, this allows any typed message",
        })
      } else {
        const typeSets = pinnedValues(fn.condition, [2]).map(decodeTypes)
        if (typeSets.some((nodes) => nodes.some((h) => AUTHORITY_TYPES[h]))) {
          const names = [
            ...new Set(
              typeSets.flat().flatMap((h) => AUTHORITY_TYPES[h] ?? [])
            ),
          ]
          hazards.push({
            ...at,
            kind: "sign-typed-message-authority",
            message: `signing ${names.join(", ")} messages authorizes actions of the avatar elsewhere: relayed transactions of Roles Modifiers where it is a member, transactions and messages of Safes it owns`,
          })
        }
        if (!domainIsolated(fn.condition, typeSets)) {
          hazards.push({
            ...at,
            kind: "sign-typed-message-domain",
            message:
              "the EIP-712 domain's chainId and verifyingContract are not both pinned: the role can sign this message type for other contracts or chains",
          })
        }
      }
    }
  }

  return hazards
}

/** Whether every way `c` passes requires `test` of the value at `path`
 *  (child indexes through Matches nodes): an Or needs it in every branch,
 *  an And in some child. */
const onPath = (
  c: Condition,
  path: readonly number[],
  test: (p: Condition) => boolean,
  depth = 0
): boolean => {
  if (c.operator === Operator.Or) {
    return (c.children ?? []).every((x) => onPath(x, path, test, depth))
  }
  if (c.operator === Operator.And) {
    return (c.children ?? []).some((x) => onPath(x, path, test, depth))
  }
  if (path.length === 0) return test(c)
  if (decodesArguments(c, depth)) {
    const p = c.children?.[path[0]]
    return p !== undefined && onPath(p, path.slice(1), test, depth + 1)
  }
  return false
}

/** An AbiEncoded Matches that decodes the arguments at this depth: after
 *  the 4-byte selector at the top level (the calldata), from the start
 *  below (an encoded struct). With other leading bytes it reads another
 *  block, so its children are not these arguments. */
const decodesArguments = (c: Condition, depth: number): boolean => {
  if (c.operator !== Operator.Matches || c.paramType !== Encoding.AbiEncoded) {
    return false
  }
  const cv = c.compValue ?? "0x"
  const leading = cv.length >= 6 ? parseInt(cv.slice(2, 6), 16) : 4
  return leading === (depth === 0 ? 4 : 0)
}

/** The EqualTo values that any branch of `c` compares at `path` with. */
const pinnedValues = (
  c: Condition,
  path: readonly number[],
  depth = 0
): string[] => {
  if (c.operator === Operator.Or || c.operator === Operator.And) {
    return (c.children ?? []).flatMap((x) => pinnedValues(x, path, depth))
  }
  if (path.length === 0) {
    return c.operator === Operator.EqualTo && c.compValue ? [c.compValue] : []
  }
  const p = decodesArguments(c, depth) ? c.children?.[path[0]] : undefined
  return p ? pinnedValues(p, path.slice(1), depth + 1) : []
}

/** Fixes a value of encoding `enc` to exact values: an EqualTo read as
 *  `enc` (another encoding compares other bytes, e.g. a word reads only the
 *  offset of `bytes`), an Or of them, or an And with one. */
const isPinned =
  (enc: Encoding) =>
  (c: Condition): boolean =>
    (c.operator === Operator.EqualTo && c.paramType === enc) ||
    (c.operator === Operator.Or && (c.children ?? []).every(isPinned(enc))) ||
    (c.operator === Operator.And && (c.children ?? []).some(isPinned(enc)))

const pinsParameter = (c: Condition, i: number, enc: Encoding) =>
  onPath(c, [i], isPinned(enc))

/** The type hashes of the struct nodes of a pinned `types` value
 *  (`abi.encode(tuple(uint256 parent, uint8 encoding, bytes32 typeHash)[])`). */
const decodeTypes = (compValue: string): string[] => {
  try {
    const [nodes] = AbiCoder.defaultAbiCoder().decode(
      ["tuple(uint256,uint8,bytes32)[]"],
      compValue
    )
    return (nodes as [bigint, bigint, string][]).map(([, , h]) =>
      h.toLowerCase()
    )
  } catch {
    return []
  }
}

const AUTHORITY_TYPES: Record<string, string> = Object.fromEntries(
  [
    "RoleTx(address to,uint256 value,bytes data,uint8 operation,bytes32 roleKey,bool shouldRevert,bytes32 salt)",
    "SafeTx(address to,uint256 value,bytes data,uint8 operation,uint256 safeTxGas,uint256 baseGas,uint256 gasPrice,address gasToken,address refundReceiver,uint256 nonce)",
    "SafeMessage(bytes message)",
  ].map((t) => [id(t).toLowerCase(), t.slice(0, t.indexOf("("))])
)

/** Field indexes of every EIP712Domain layout (fields in the order
 *  EIP-712 defines), by type hash. */
const DOMAIN_LAYOUTS: Record<string, { chainId?: number; contract?: number }> =
  (() => {
    const fields = [
      ["string name", "name"],
      ["string version", "version"],
      ["uint256 chainId", "chainId"],
      ["address verifyingContract", "contract"],
      ["bytes32 salt", "salt"],
    ] as const
    const layouts: Record<string, { chainId?: number; contract?: number }> = {}
    for (let mask = 1; mask < 32; mask++) {
      const present = fields.filter((_, i) => mask & (1 << i))
      const layout: { chainId?: number; contract?: number } = {}
      present.forEach(([, key], i) => {
        if (key === "chainId") layout.chainId = i
        if (key === "contract") layout.contract = i
      })
      const hash = id(
        `EIP712Domain(${present.map(([f]) => f).join(",")})`
      ).toLowerCase()
      layouts[hash] = layout
    }
    return layouts
  })()

/** Whether every way the condition passes pins the domain's chainId and
 *  verifyingContract, for the domain layout of the pinned types. */
const domainIsolated = (c: Condition, typeSets: string[][]): boolean => {
  const layouts = typeSets.map((hashes) =>
    hashes.map((h) => DOMAIN_LAYOUTS[h]).find(Boolean)
  )
  const layout = layouts[0]
  if (
    !layout ||
    layouts.some(
      (l) =>
        !l || l.chainId !== layout.chainId || l.contract !== layout.contract
    )
  ) {
    return false // unknown or differing domain layouts
  }
  // without either field, signatures are valid for other contracts or chains
  if (layout.contract === undefined || layout.chainId === undefined) {
    return false
  }
  const pinned = (i: number) => onPath(c, [0, i], isPinned(Encoding.Static))
  return pinned(layout.chainId) && pinned(layout.contract)
}
