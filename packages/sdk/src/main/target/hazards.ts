import {
  Clearance,
  Condition,
  Encoding,
  ExecutionOptions,
  Operator,
  Target,
} from "../types"
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
 * - `sign-typed-message-domain`: a typed-message permission that leaves the
 *   EIP-712 domain unconstrained, so the role can sign that message type for
 *   every contract that uses it.
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
        if (!fn.condition || !pinsParameter(fn.condition, 0)) {
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
      if (!fn.condition || !pinsParameter(fn.condition, 2)) {
        hazards.push({
          ...at,
          kind: "sign-typed-message-types",
          message:
            "the signing library accepts typed messages under any selector: without pinning `types`, this allows any typed message",
        })
      } else if (!constrainsParameter(fn.condition, 0)) {
        hazards.push({
          ...at,
          kind: "sign-typed-message-domain",
          message:
            "the EIP-712 domain is not constrained: the role can sign this message type for every contract that uses it",
        })
      }
    }
  }

  return hazards
}

/** Whether every way `c` passes requires `test` of parameter `i` of the
 *  calldata: an Or needs it in every branch, an And in some child. */
const onParameter = (
  c: Condition,
  i: number,
  test: (p: Condition) => boolean
): boolean => {
  if (c.operator === Operator.Or) {
    return (c.children ?? []).every((x) => onParameter(x, i, test))
  }
  if (c.operator === Operator.And) {
    return (c.children ?? []).some((x) => onParameter(x, i, test))
  }
  if (c.paramType === Encoding.AbiEncoded && c.operator === Operator.Matches) {
    const p = c.children?.[i]
    return p !== undefined && test(p)
  }
  return false
}

/** Fixes the value to exact values: EqualTo, an Or of them, or an And with
 *  one. */
const isPinned = (c: Condition): boolean =>
  c.operator === Operator.EqualTo ||
  (c.operator === Operator.Or && (c.children ?? []).every(isPinned)) ||
  (c.operator === Operator.And && (c.children ?? []).some(isPinned))

/** Checks anything at all: a node other than Pass and a plain Matches (an
 *  AbiEncoded Matches with a prefix checks it). */
const hasCheck = (c: Condition): boolean =>
  (c.operator !== Operator.Pass && c.operator !== Operator.Matches) ||
  (c.operator === Operator.Matches && (c.compValue?.length ?? 0) > 6) ||
  (c.children ?? []).some(hasCheck)

const pinsParameter = (c: Condition, i: number) => onParameter(c, i, isPinned)
const constrainsParameter = (c: Condition, i: number) =>
  onParameter(c, i, hasCheck)
