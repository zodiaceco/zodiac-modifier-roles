// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "./Storage.sol";

/**
 * @title   Membership
 * @notice  Validates that a module holds an active role membership before
 *          authorizing transactions. Memberships can be time-bound and
 *          usage-limited.
 *
 * @dev     Module authentication is enforced at the public entry points via
 *          `moduleOnly` / `moduleOnlySigned` (defined in `Modifier`). This
 *          function reads `sentOrSignedByModule()` to identify the active
 *          module and verifies its membership for the requested role.
 *          Membership packs timestamps and uses into a single uint256.
 *          See layout below.
 *
 * @author  gnosisguild
 */

abstract contract Membership is RolesStorage {
    uint256 private constant _MEMBERSHIP_NOOP = type(uint256).max;
    uint256 private constant _MEMBERSHIP_REVOKE = 0;

    function _authenticate(
        bytes32 roleKey
    ) internal view returns (address module, uint256 nextMembership) {
        // Never authorize the zero role
        if (roleKey == 0) {
            revert NoMembership();
        }

        module = sentOrSignedByModule();

        uint256 membership = roles[roleKey].members[module];
        if (membership == 0) {
            revert NoMembership();
        }

        /*
         * Membership Layout (256 bits)
         * ┌────────────────┬────────────────┬─────────────────────────────────┐
         * │ startTimestamp │  endTimestamp  │            usesLeft             │
         * │    64 bits     │    64 bits     │            128 bits             │
         * └────────────────┴────────────────┴─────────────────────────────────┘
         *
         * - startTimestamp: Unix timestamp when membership becomes valid
         * - endTimestamp:   Unix timestamp when membership expires
         * - usesLeft:       Remaining uses (type(uint128).max = unlimited)
         */

        if (block.timestamp < uint64(membership >> 192)) {
            revert MembershipNotYetValid();
        }
        if (block.timestamp > uint64(membership >> 128)) {
            revert MembershipExpired();
        }
        if (~membership << 128 == 0) {
            // unlimited uses
            return (module, _MEMBERSHIP_NOOP);
        }

        uint256 usesLeft = (membership << 128) >> 128;

        return (
            module,
            usesLeft <= 1
                ? _MEMBERSHIP_REVOKE
                : ((membership >> 128) << 128) | (usesLeft - 1)
        );
    }

    function _hasActiveMembership(
        bytes32 roleKey,
        address module
    ) internal view returns (bool) {
        if (roleKey == 0) return false;
        uint256 membership = roles[roleKey].members[module];
        if (membership == 0) return false;
        if (block.timestamp < uint64(membership >> 192)) return false;
        if (block.timestamp > uint64(membership >> 128)) return false;
        return true;
    }
}
