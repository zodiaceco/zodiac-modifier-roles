// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {ExecutionOptions} from "./Permission.sol";

/**
 * @title IRolesEvent - All events emitted by the Roles Mod.
 *
 * @author gnosisguild
 */
interface IRolesEvent {
    /*//////////////////////////////////////////////////////////////
                             SETUP EVENTS
    //////////////////////////////////////////////////////////////*/

    /// Emitted when the Roles Mod is initialized
    event RolesModSetup(
        address indexed initiator,
        address indexed owner,
        address indexed avatar,
        address target,
        string version
    );

    /// Emitted when a role is granted to a module
    event GrantRole(
        bytes32 roleKey,
        address module,
        uint64 start,
        uint64 end,
        uint128 usesLeft
    );

    /// Emitted when a role is revoked from a module
    event RevokeRole(bytes32 roleKey, address module);

    /// Emitted when role membership is updated (e.g., uses consumed)
    event UpdateRole(
        bytes32 roleKey,
        address module,
        uint64 start,
        uint64 end,
        uint128 usesLeft
    );

    /// Emitted when the default role is set for a module
    event SetDefaultRole(address module, bytes32 defaultRoleKey);

    /*//////////////////////////////////////////////////////////////
                           PERMISSION EVENTS
    //////////////////////////////////////////////////////////////*/

    /// Emitted when a target address is allowed for a role
    event AllowTarget(
        bytes32 roleKey,
        address targetAddress,
        bytes conditions,
        ExecutionOptions options
    );

    /// Emitted when a target address is revoked from a role
    event RevokeTarget(bytes32 roleKey, address targetAddress);

    /// Emitted when a target is scoped (function-level permissions enabled)
    event ScopeTarget(bytes32 roleKey, address targetAddress);

    /// Emitted when a function is allowed for a role
    event AllowFunction(
        bytes32 roleKey,
        address targetAddress,
        bytes4 selector,
        bytes conditions,
        ExecutionOptions options
    );

    /// Emitted when a function is allowed globally (applies to all targets)
    event AllowFunctionGlobally(
        bytes32 roleKey,
        bytes4 selector,
        bytes conditions
    );

    /// Emitted when a function is revoked from a role
    event RevokeFunction(
        bytes32 roleKey,
        address targetAddress,
        bytes4 selector
    );

    /// Emitted when a globally allowed function is revoked
    event RevokeFunctionGlobally(bytes32 roleKey, bytes4 selector);

    /// Emitted when an allowance is configured
    event SetAllowance(
        bytes32 allowanceKey,
        uint128 balance,
        uint128 maxRefill,
        uint128 refill,
        uint64 period,
        uint64 timestamp
    );

    /// Emitted when a transaction unwrap adapter is set
    event SetUnwrapAdapter(address to, bytes4 selector, address adapter);

    /*//////////////////////////////////////////////////////////////
                           ALLOWANCE EVENTS
    //////////////////////////////////////////////////////////////*/

    /// Emitted when an allowance is consumed during execution
    event ConsumeAllowance(
        bytes32 allowanceKey,
        uint128 consumed,
        uint128 newBalance
    );
}
