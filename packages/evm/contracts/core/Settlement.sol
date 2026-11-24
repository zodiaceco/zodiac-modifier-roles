// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Consumption} from "../IEvaluator.sol";
import "./Storage.sol";

/**
 * @title   Settlement
 * @notice  Accrues allowances and persists allowance consumption and membership
 *          updates to storage.
 *
 * @dev     Invoked after successful execution. Reentrancy is prevented by the
 *          nonReentrant modifier on execution entry points.
 *
 * @author  gnosisguild
 */
abstract contract Settlement is RolesStorage {
    /**
     * @dev Settles allowance consumption and membership updates after a successful execution.
     *
     * @param sender The address that initiated the transaction
     * @param roleKey The role key used for execution
     * @param consumptions Allowance consumption records to settle
     */
    function _settle(
        address sender,
        bytes32 roleKey,
        Consumption[] memory consumptions
    ) internal {
        uint256 count = consumptions.length;
        for (uint256 i; i < count; ++i) {
            Consumption memory consumption = consumptions[i];

            uint128 updatedBalance = _consume(
                consumption.allowanceKey,
                consumption.consumed
            );

            emit ConsumeAllowance(
                consumption.allowanceKey,
                consumption.consumed,
                updatedBalance
            );
        }

        /*
         * Re-read membership after execution, in case the call revoked,
         * renounced or updated it.
         *
         * Nothing to settle if it was cleared or has unlimited uses.
         */
        uint256 membership = roles[roleKey].members[sender];
        if (membership == 0 || (~membership << 128) == 0) return;

        uint128 usesLeft = uint128(membership);
        uint256 nextMembership = usesLeft <= 1 ? 0 : membership - 1;

        roles[roleKey].members[sender] = nextMembership;
        if (nextMembership != 0) {
            emit UpdateRole(
                roleKey,
                sender,
                uint64(nextMembership >> 192),
                uint64(nextMembership >> 128),
                uint128(nextMembership)
            );
        } else {
            emit RevokeRole(roleKey, sender);
        }
    }

    /// @dev Calculates an allowance's accrued balance and timestamp at
    ///      `blockTimestamp` from Core storage.
    function _accrue(
        bytes32 allowanceKey,
        uint64 blockTimestamp
    ) private view returns (uint128 balance, uint64 timestamp) {
        Allowance memory a = allowances[allowanceKey];

        // No refill configured.
        if (a.period == 0) return (a.balance, a.timestamp);

        // Nothing accrues when the configured timestamp is current or in the future.
        // This also makes the elapsed-time subtraction below safe.
        if (blockTimestamp <= a.timestamp) return (a.balance, a.timestamp);

        // Calculate full periods elapsed.
        uint64 elapsedIntervals = (blockTimestamp - a.timestamp) / a.period;
        if (elapsedIntervals == 0) return (a.balance, a.timestamp);

        // Timestamp always advances, even when balance is at cap
        timestamp = a.timestamp + elapsedIntervals * a.period;

        // Already at cap, or initial balance was set above maxRefill
        if (a.balance >= a.maxRefill) return (a.balance, timestamp);

        // Add refill for each elapsed period, capping at maxRefill.
        uint256 accruedBalance = uint256(a.balance) +
            uint256(a.refill) *
            elapsedIntervals;
        balance = accruedBalance < a.maxRefill
            ? uint128(accruedBalance)
            : a.maxRefill;
    }

    /// @dev Re-accrues the allowance from Core storage, deducts `consumed`,
    ///      writes back balance and timestamp, and returns the new balance.
    function _consume(
        bytes32 allowanceKey,
        uint128 consumed
    ) private returns (uint128 updatedBalance) {
        (uint128 balance, uint64 _timestamp) = _accrue(
            allowanceKey,
            uint64(block.timestamp)
        );
        if (consumed > balance) {
            revert AllowanceExceeded(allowanceKey);
        }
        updatedBalance = balance - consumed;

        /*
         * Allowance Storage Layout (2 words):
         * ┌────────────────────────────────┬────────────────────────────────┐
         * │           maxRefill            │             refill             │
         * │            128 bits            │            128 bits            │
         * ├────────────────┬───────────────┴───────────────┬────────────────┤
         * │   timestamp    │            balance            │     period     │
         * │    64 bits     │           128 bits            │    64 bits     │
         * └────────────────┴───────────────────────────────┴────────────────┘
         */
        assembly {
            mstore(0x00, allowanceKey)
            mstore(0x20, allowances.slot)

            let slot := add(keccak256(0x00, 0x40), 1)

            sstore(
                slot,
                or(
                    or(shl(192, _timestamp), shl(64, updatedBalance)),
                    and(sload(slot), 0xffffffffffffffff)
                )
            )
        }
    }

    /*//////////////////////////////////////////////////////////////
                                VIEWS
    //////////////////////////////////////////////////////////////*/

    /// @dev Returns a module's membership of a role.
    /// @param module Address of the module
    /// @param roleKey Identifier of the role
    /// @return active Whether the module can currently execute under the
    ///         role: it is enabled and the membership is within its validity
    ///         window
    /// @return start Timestamp from which the membership is valid
    /// @return end Timestamp until which it is valid (uint64 max = no expiry)
    /// @return usesLeft Remaining uses (uint128 max = unlimited)
    function membershipOf(
        address module,
        bytes32 roleKey
    )
        external
        view
        returns (bool active, uint64 start, uint64 end, uint128 usesLeft)
    {
        uint256 membership = roles[roleKey].members[module];
        start = uint64(membership >> 192);
        end = uint64(membership >> 128);
        usesLeft = uint128(membership);

        active =
            roleKey != 0 &&
            membership != 0 &&
            block.timestamp >= start &&
            block.timestamp <= end &&
            isModuleEnabled(module);
    }

    /// @dev Returns the accrued allowance balance at current block.timestamp.
    ///      Read by the Evaluator (see IRolesCore).
    /// @param allowanceKey The allowance key.
    /// @return balance The accrued balance.
    /// @return timestamp The timestamp of the last accrual point.
    function accruedAllowance(
        bytes32 allowanceKey
    ) external view returns (uint128 balance, uint64 timestamp) {
        return _accrue(allowanceKey, uint64(block.timestamp));
    }
}
