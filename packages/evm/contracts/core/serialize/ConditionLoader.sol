// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../common/ImmutableStorage.sol";

import "./ConditionUnpacker.sol";

import "../../types/Types.sol";

/**
 * @title ConditionLoader
 * @notice Loads and unpacks condition trees from immutable storage.
 *
 * @author gnosisguild
 */
library ConditionLoader {
    /**
     * @param scopeConfig Packed scopeSonfig (options << 160 | pointer).
     * @return condition The unpacked condition tree with embedded layout.
     * @return maxPluckIndex Maximum pluck index for pluck bag allocation.
     */
    function load(
        uint256 scopeConfig
    )
        internal
        view
        returns (Condition memory condition, uint256 maxPluckIndex)
    {
        address pointer = address(uint160(scopeConfig));
        bytes memory buffer = ImmutableStorage.load(pointer);
        return ConditionUnpacker.unpack(buffer);
    }
}
