import { hexlify, toUtf8Bytes } from "ethers"
import { Encoding, Operator } from "../types"
import { SIGN_TYPED_MESSAGE_LIB_ADDRESS } from "../addresses"

/**
 * Returns a permission allowing the role to sign `personal_sign` messages
 * whose text starts with the given string.
 *
 * Targets the `personalSign(bytes)` entrypoint of `SignTypedMessageLib`, which
 * handles the EIP-191 wrapping internally. The condition is a single bitmask
 * on the raw message bytes.
 *
 * @param params
 * @param params.startsWith - Prefix string the message text must begin with.
 *   Must be non-empty — an empty prefix would allow signing arbitrary
 *   messages, which should generally not be delegated.
 * @returns A permission targeting `SignTypedMessageLib` with the
 *   `personalSign(bytes)` selector, delegatecall flag, and the prefix
 *   bitmask condition.
 */
export const allowPersonalSign = ({ startsWith }: { startsWith: string }) => {
  if (!startsWith) {
    throw new Error("startsWith must not be empty")
  }

  const startsWithHex = hexlify(toUtf8Bytes(startsWith)).slice(2)
  const shift = "0000"
  const mask = "ff".repeat(startsWithHex.length / 2)
  const compValue = `0x${shift}${mask}${startsWithHex}` as `0x${string}`

  return {
    targetAddress: SIGN_TYPED_MESSAGE_LIB_ADDRESS,
    selector: "0x641e3d2b" as const, // personalSign(bytes)
    delegatecall: true,
    condition: {
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Dynamic,
          operator: Operator.Bitmask,
          compValue,
        },
      ],
    },
  }
}
