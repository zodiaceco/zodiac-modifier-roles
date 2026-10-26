// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../common/ImmutableStorage.sol";

import "./ConditionPacker.sol";
import "./Integrity.sol";

import "../../types/Types.sol";

/**
 * @title ConditionStorer
 * @notice Packs condition trees and stores packed buffers in immutable storage.
 *
 * @author gnosisguild
 */
library ConditionStorer {
    /**
     * @notice Validates and packs a condition tree into bytes.
     *
     * @param conditions The flat condition array in BFS order.
     * @return buffer The packed condition buffer.
     */
    function pack(
        ConditionFlat[] memory conditions
    ) external pure returns (bytes memory buffer) {
        Integrity.enforce(conditions);
        return ConditionPacker.pack(conditions);
    }

    /**
     * @notice Stores a pre-packed condition buffer.
     *
     * @param buffer The packed condition buffer.
     * @param options Execution options (Send, DelegateCall, Both, None).
     * @return scopeConfig Packed scope config (options << 160 | pointer).
     */
    function store(
        bytes memory buffer,
        ExecutionOptions options
    ) external returns (uint256 scopeConfig) {
        address pointer = ImmutableStorage.store(buffer);
        return (uint256(options) << 160) | uint160(pointer);
    }
}
