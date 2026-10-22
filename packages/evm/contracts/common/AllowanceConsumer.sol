// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {ALLOWANCES_SLOT} from "../core/StorageSlots.sol";
import {Allowance, Consumption} from "../types/Allowance.sol";
import {Status} from "../types/Authorization.sol";

/**
 * @title AllowanceConsumer
 * @notice Loads allowances from storage and tracks their consumption.
 *
 * @dev Owns the running consumption list threaded through permission
 *      evaluation. An entry tracks one allowance key: the balance accrued
 *      when first touched, and the amount consumed since.
 *
 *      The list is immutable. Updates produce a new list via _copyOnWrite,
 *      which copies entry POINTERS (a struct array in memory is an array of
 *      references), so unchanged entries are shared between the old and new
 *      list. Entries must therefore never be mutated in place: _findOrAccrue
 *      returns a newly allocated entry, consume adds the amount to its
 *      consumed total, and _copyOnWrite shallow-copies the list and writes
 *      the updated entry in. This keeps a failed branch's consumption from
 *      leaking into sibling branches sharing the same list.
 *
 * @author gnosisguild
 */
library AllowanceConsumer {
    /**
     * @notice Consumes `amount` from an allowance in the running list.
     * @param consumptions Running consumption list (not mutated)
     * @param allowanceKey The allowance to consume from
     * @param amount Amount to consume, denominated in balance units
     * @return status Ok, or AllowanceExceeded when the amount does not fit
     * @return next Updated list when status is Ok, the input list otherwise
     */
    function consume(
        Consumption[] memory consumptions,
        bytes32 allowanceKey,
        uint256 amount
    ) internal view returns (Status status, Consumption[] memory next) {
        (Consumption memory entry, uint256 index) = _findOrAccrue(
            consumptions,
            allowanceKey
        );

        if (amount > entry.balance - entry.consumed) {
            return (Status.AllowanceExceeded, consumptions);
        }
        // Fits uint128: amount is capped at balance - consumed.
        entry.consumed += uint128(amount);

        return (Status.Ok, _copyOnWrite(consumptions, entry, index));
    }

    /**
     * @notice Loads an allowance from storage and calculates its accrued
     *         balance at `blockTimestamp`.
     */
    function accrue(
        bytes32 allowanceKey,
        uint64 blockTimestamp
    ) internal view returns (uint128 balance, uint64 timestamp) {
        Allowance memory a = _load(allowanceKey);

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

    /**
     * @dev Finds the entry tracking `allowanceKey`, accruing it from storage
     *      when the key is not tracked yet.
     *
     *      Returns a newly allocated Consumption entry, never a reference
     *      into the list: entries are pointer-shared across list copies, so
     *      callers must update the copy and write it back with _copyOnWrite.
     *
     * @return entry Tracked (or newly accrued) entry
     * @return index Position of the entry; equals consumptions.length when new
     */
    function _findOrAccrue(
        Consumption[] memory consumptions,
        bytes32 allowanceKey
    ) private view returns (Consumption memory entry, uint256 index) {
        for (; index < consumptions.length; ++index) {
            if (consumptions[index].allowanceKey == allowanceKey) break;
        }

        if (index < consumptions.length) {
            Consumption memory tracked = consumptions[index];
            return (
                Consumption(
                    allowanceKey,
                    tracked.balance,
                    tracked.consumed,
                    tracked.timestamp
                ),
                index
            );
        }

        (uint128 balance, uint64 timestamp) = accrue(
            allowanceKey,
            uint64(block.timestamp)
        );
        return (Consumption(allowanceKey, balance, 0, timestamp), index);
    }

    /**
     *
     * Storage Layout (2 words, 64 bytes, 512 bits):
     * ┌────────────────────────────────┬────────────────────────────────┐
     * │           maxRefill            │             refill             │
     * │            128 bits            │            128 bits            │
     * ├────────────────┬───────────────┴───────────────┬────────────────┤
     * │   timestamp    │            balance            │     period     │
     * │    64 bits     │           128 bits            │    64 bits     │
     * └────────────────┴───────────────────────────────┴────────────────┘
     *
     */
    function _load(
        bytes32 allowanceKey
    ) private view returns (Allowance memory) {
        uint256 word1;
        uint256 word2;
        assembly {
            mstore(0x00, allowanceKey)
            mstore(0x20, ALLOWANCES_SLOT)
            let slot := keccak256(0x00, 0x40)
            word1 := sload(slot)
            word2 := sload(add(slot, 1))
        }

        return
            Allowance({
                refill: uint128(word1),
                maxRefill: uint128(word1 >> 128),
                period: uint64(word2),
                balance: uint128(word2 >> 64),
                timestamp: uint64(word2 >> 192)
            });
    }

    /**
     * @dev Creates a new list with `entry` written at `index`. When index
     *      equals the list length, the list grows by one.
     *
     *      Shallow: entry pointers are shared with the source list, so
     *      entries must be treated as immutable (see library note).
     */
    function _copyOnWrite(
        Consumption[] memory consumptions,
        Consumption memory entry,
        uint256 index
    ) private pure returns (Consumption[] memory result) {
        uint256 prevLength = consumptions.length;
        uint256 length = prevLength + (index == prevLength ? 1 : 0);

        assembly {
            // Allocate new array
            result := mload(0x40)
            mstore(0x40, add(result, mul(add(length, 1), 0x20)))
            mstore(result, length)

            // Shallow copy previous elements
            let dst := add(result, 0x20)
            let src := add(consumptions, 0x20)
            let size := mul(prevLength, 0x20)
            mcopy(dst, src, size)
        }

        result[index] = entry;
    }
}
