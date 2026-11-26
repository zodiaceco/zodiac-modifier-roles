// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Operation} from "@gnosis-guild/zodiac-core/contracts/core/Operation.sol";

import "../../IEvaluator.sol";
import "../../evaluator/AbiLocation.sol";
import "../../evaluator/Engine.sol";
import "../../evaluator/Integrity.sol";
import "../../evaluator/serialize/Packer.sol";
import "../../evaluator/serialize/Unpacker.sol";
import "../../evaluator/types/EvaluatorError.sol";
import "../../evaluator/types/EvaluatorTypes.sol";

/**
 * @dev Runs a full condition tree (Integrity → pack → unpack → evaluate) on
 *      calldata, without storage or allowances.
 */
contract MockEvaluator is IRolesCore, IEvaluatorError {
    mapping(bytes32 => uint128) private _balances;

    function avatar() external pure override returns (address) {
        return address(0);
    }

    function accruedAllowance(
        bytes32 allowanceKey
    ) external view override returns (uint128 balance, uint64 timestamp) {
        return (_balances[allowanceKey], type(uint64).max);
    }

    function evaluate(
        bytes calldata data,
        ConditionFlat[] memory conditions
    ) public view returns (Status) {
        Integrity.enforce(conditions);
        return evaluateUnchecked(data, conditions);
    }

    function evaluateWith(
        bytes calldata data,
        ConditionFlat[] memory conditions,
        uint256 value,
        bytes32[] memory keys,
        uint128[] memory balances
    ) public returns (Status, Consumption[] memory) {
        Integrity.enforce(conditions);
        return
            evaluatePackedWith(
                data,
                Packer.pack(conditions),
                value,
                keys,
                balances
            );
    }

    function evaluatePackedWith(
        bytes calldata data,
        bytes memory packed,
        uint256 value,
        bytes32[] memory keys,
        uint128[] memory balances
    ) public returns (Status, Consumption[] memory) {
        for (uint256 i; i < keys.length; ++i) {
            _balances[keys[i]] = balances[i];
        }

        (Condition memory root, uint256 maxPluck) = Unpacker.unpack(
            packed,
            address(this)
        );
        Context memory context = Context({
            core: address(this),
            to: address(this),
            value: value,
            data: AbiLocation.toSpan(data),
            operation: Operation.Call,
            pluckedValues: new bytes32[](maxPluck),
            pluckedLocations: new Span[](maxPluck)
        });
        Result memory result = Engine.evaluate(
            root,
            new Consumption[](0),
            context
        );
        return (Status(result.status), result.consumptions);
    }

    /// @dev Reverts with Integrity's error if it rejects `conditions`.
    function enforceIntegrity(ConditionFlat[] memory conditions) public pure {
        Integrity.enforce(conditions);
    }

    /// @dev Without Integrity, as for trees stored with the `...Packed`
    ///      setters.
    function evaluateUnchecked(
        bytes calldata data,
        ConditionFlat[] memory conditions
    ) public view returns (Status) {
        bytes memory packed = Packer.pack(conditions);
        (Condition memory root, uint256 maxPluck) = Unpacker.unpack(
            packed,
            address(this)
        );

        Context memory context = Context({
            core: address(this),
            to: address(this),
            value: 0,
            data: AbiLocation.toSpan(data),
            operation: Operation.Call,
            pluckedValues: new bytes32[](maxPluck),
            pluckedLocations: new Span[](maxPluck)
        });

        return
            Status(Engine.evaluate(root, new Consumption[](0), context).status);
    }
}
