// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.21 <0.9.0;

import "../../periphery/signing/SignTypedMessageLib.sol";

/// Exposes `SignTypedMessageLib`'s file-level `uintToString`.
contract MockUintToString {
    function asString(uint256 value) external pure returns (string memory) {
        return uintToString(value);
    }
}
