// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 GG DAO LLC
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../core/evaluate/ConditionEvaluator.sol";
import "../../core/serialize/Integrity.sol";
import "../../core/serialize/ConditionPacker.sol";
import "../../core/serialize/ConditionUnpacker.sol";
import "../../types/Types.sol";

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
