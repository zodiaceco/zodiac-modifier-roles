import { BigNumberish, BytesLike, getAddress, hexlify, ParamType } from "ethers"
import { Encoding, Operator } from "../../../types"
import { AVATAR_IS_OWNER_OF_ERC721_ADDRESS } from "../../../addresses"

import { ConditionFunction } from "../types"

/**
 * Asserts that the value is scope represents an ERC721 token ID owned by the avatar.
 * Assumes that the call target is the ERC721 contract.
 */
export const avatarIsOwnerOfErc721: ConditionFunction<BigNumberish> = (
  abiType: ParamType
) => {
  if (abiType.type !== "uint256") {
    throw new Error(
      "`avatarIsOwnerOfErc721` is only supported for uint256 params"
    )
  }
  if (BigInt(AVATAR_IS_OWNER_OF_ERC721_ADDRESS) === 0n) {
    throw new Error(
      "`avatarIsOwnerOfErc721` is not available yet: the v3 AvatarIsOwnerOfERC721 checker is not deployed"
    )
  }
  return {
    paramType: Encoding.Static,
    operator: Operator.Custom,
    compValue: encodeCustomCompValue(AVATAR_IS_OWNER_OF_ERC721_ADDRESS),
  }
}

const encodeCustomCompValue = (
  customConditionAddress: `0x${string}`,
  extra: BytesLike = "0x"
) => {
  const extraHex = hexlify(extra).slice(2)
  return (getAddress(customConditionAddress).toLowerCase() +
    extraHex) as `0x${string}`
}
