/**
 * Deployment addresses for Zodiac Roles periphery contracts.
 *
 * Mastercopy deployments use deterministic CREATE2 deployment so the
 * address is the same on every chain.
 */

export const SIGN_TYPED_MESSAGE_LIB_ADDRESS =
  "0xD8E9A20F9fDcaE4e6390cc0724D88853C50D07e3"

// TODO: replace with the actual deterministic deployment address once published
// (the v2 checker at 0x91B1bd7BCC5E623d5CE76b0152253499a9C819d1 implements
// the v2 `ICustomCondition` and fails every v3 check)
export const AVATAR_IS_OWNER_OF_ERC721_ADDRESS =
  "0x0000000000000000000000000000000000000000"
