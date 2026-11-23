// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Operation} from "@gnosis-guild/zodiac-core/contracts/core/Operation.sol";

import "../IEvaluator.sol";
import "../ImmutableStorage.sol";

import "./AbiLocation.sol";
import "./Engine.sol";
import "./Integrity.sol";
import "./serialize/Packer.sol";
import "./serialize/Unpacker.sol";
import "./types/EvaluatorError.sol";
import "./types/EvaluatorTypes.sol";

/**
 * @title Evaluator
 * @notice Stateless, replaceable condition evaluator and serializer for the
 *         Zodiac Roles Mod.
 *
 * @dev Invoked via staticcall by a Roles Core contract. Owns the packed
 *      condition format (integrity validation, packing, and unpacking) and has
 *      no storage of its own: reads packed condition trees from the immutable
 *      pointer encoded in `scopeConfig`, and reads dynamic Core state (avatar,
 *      accrued allowances) via view calls back to `msg.sender` (Core).
 */
contract Evaluator is IEvaluator, IEvaluatorError {
    /// @inheritdoc IEvaluator
    function evaluate(
        uint256 scopeConfig,
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        Consumption[] memory consumptions
    ) external view override returns (Result memory) {
        address pointer = address(uint160(scopeConfig));
        bytes memory buffer = ImmutableStorage.load(pointer);
        if (buffer.length == 0) {
            return Result(0, 0, 0, consumptions);
        }

        (Condition memory condition, uint256 maxPluckCount) = Unpacker.unpack(
            buffer,
            msg.sender
        );

        return
            Engine.evaluate(
                condition,
                consumptions,
                Context(
                    msg.sender,
                    to,
                    value,
                    AbiLocation.toSpan(data),
                    operation,
                    new bytes32[](maxPluckCount),
                    new Span[](maxPluckCount)
                )
            );
    }

    /// @inheritdoc IEvaluator
    function pack(
        ConditionFlat[] memory conditions
    ) external pure override returns (bytes memory buffer) {
        Integrity.enforce(conditions);
        return Packer.pack(conditions);
    }
}
