// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "@gnosis-guild/zodiac-core/contracts/core/Modifier.sol";

import "../types/Types.sol";

/**
 * @title RolesStorage
 * @notice Base contract defining shared storage for Zodiac Roles Mod
 *
 * @author gnosisguild
 *
 */
abstract contract RolesStorage is Modifier, IRolesEvent, IRolesError {
    string public constant VERSION = "3.0.0";

    mapping(bytes32 => Role) internal roles;
    mapping(bytes32 => Allowance) public allowances;
    mapping(bytes32 => address) public unwrappers;
    mapping(address => bytes32) public defaultRoles;

    bool private transient _reentrancyGuard;

    modifier nonReentrant() {
        if (_reentrancyGuard) {
            revert Reentrancy();
        }
        _reentrancyGuard = true;
        _;
        _reentrancyGuard = false;
    }

    function _key(
        address targetAddress,
        bytes4 selector
    ) internal pure returns (bytes32) {
        return bytes32(bytes20(targetAddress)) | (bytes32(selector) >> 160);
    }
}
