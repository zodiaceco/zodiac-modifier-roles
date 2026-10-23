// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../core/evaluate/ConditionEvaluator.sol";
import "../../core/serialize/Integrity.sol";
import "../../core/serialize/ConditionPacker.sol";
import "../../core/serialize/ConditionUnpacker.sol";
import "../../types/Types.sol";
import {ALLOWANCES_SLOT} from "../../core/StorageSlots.sol";

/**
 * @dev Runs a full condition tree (Integrity → pack → unpack → evaluate) on
 *      calldata, without storage or allowances. Used by the formal-model
 *      tests to check `evaluate` against the ABI spec end to end.
 */
contract MockEvaluator {
    function evaluate(
        bytes calldata data,
        ConditionFlat[] memory conditions
    ) public view returns (Status) {
        Integrity.enforce(conditions);
        return evaluateUnchecked(data, conditions);
    }

    /// @dev For the Lean model of `evaluate` (test/formal/integrity-gaps.spec.ts,
    ///      `GAP_EVAL`): sets allowance balances (no refill), then runs
    ///      Integrity → pack → unpack → evaluate with `msg.value` = `value`.
    ///      Call it with `staticCall`.
    function evaluateWith(
        bytes calldata data,
        ConditionFlat[] memory conditions,
        uint256 value,
        bytes32[] memory keys,
        uint128[] memory balances
    ) public returns (Status, Consumption[] memory) {
        for (uint256 i; i < keys.length; ++i) {
            bytes32 key = keys[i];
            // word2: timestamp (max, so nothing accrues) | balance | period 0
            uint256 word2 = (uint256(type(uint64).max) << 192) |
                (uint256(balances[i]) << 64);
            assembly {
                mstore(0x00, key)
                mstore(0x20, ALLOWANCES_SLOT)
                let slot := keccak256(0x00, 0x40)
                sstore(slot, 0)
                sstore(add(slot, 1), word2)
            }
        }

        Integrity.enforce(conditions);
        bytes memory packed = ConditionPacker.pack(conditions);
        (Condition memory root, uint256 maxPluck) = ConditionUnpacker.unpack(
            packed
        );
        Context memory context = Context({
            to: address(this),
            value: value,
            operation: Operation.Call,
            pluckedValues: new bytes32[](maxPluck),
            pluckedLocations: new uint256[](maxPluck)
        });
        Result memory result = ConditionEvaluator.evaluate(
            data,
            0,
            root,
            new Consumption[](0),
            context
        );
        return (result.status, result.consumptions);
    }

    /// @dev Without Integrity, as for trees stored with the `...Packed`
    ///      setters.
    function evaluateUnchecked(
        bytes calldata data,
        ConditionFlat[] memory conditions
    ) public view returns (Status) {
        bytes memory packed = ConditionPacker.pack(conditions);
        (Condition memory root, uint256 maxPluck) = ConditionUnpacker.unpack(
            packed
        );

        Context memory context = Context({
            to: address(this),
            value: 0,
            operation: Operation.Call,
            pluckedValues: new bytes32[](maxPluck),
            pluckedLocations: new uint256[](maxPluck)
        });

        return
            ConditionEvaluator
                .evaluate(data, 0, root, new Consumption[](0), context)
                .status;
    }
}
