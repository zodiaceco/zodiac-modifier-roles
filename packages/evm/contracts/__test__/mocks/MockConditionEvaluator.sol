// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../core/evaluate/ConditionEvaluator.sol";
import "../../types/Types.sol";

contract MockConditionEvaluator is IRolesError {
    function evaluate(
        bytes calldata data,
        Operator op
    ) external view returns (Status) {
        Condition memory condition;
        condition.index = 7;
        condition.operator = op;

        Consumption[] memory consumptions = new Consumption[](0);
        Context memory context = Context({
            to: address(this),
            value: 0,
            operation: Operation.Call,
            pluckedValues: new bytes32[](0),
            pluckedLocations: new uint256[](0)
        });

        return
            ConditionEvaluator
                .evaluate(data, 0, condition, consumptions, context)
                .status;
    }
}
