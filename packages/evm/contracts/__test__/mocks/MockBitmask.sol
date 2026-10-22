// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../core/evaluate/BitmaskChecker.sol";
import "../../types/Types.sol";

/**
 * @dev Exposes `BitmaskChecker.check`. Used by the formal-model tests to
 *      compare it with its Lean transcription.
 */
contract MockBitmask {
    function check(
        bytes calldata data,
        uint256 location,
        bytes memory compValue,
        bool inlined,
        uint256 size
    ) public pure returns (Status) {
        return BitmaskChecker.check(data, location, compValue, inlined, size);
    }
}
