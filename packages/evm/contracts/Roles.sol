// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "./core/Authorization.sol";
import "./core/Membership.sol";
import "./core/RoleTx.sol";
import "./core/Settlement.sol";
import "./core/Setup.sol";

/**
 * @title Zodiac Roles Mod - granular, role-based access control and policy
 *        engine for onchain accounts
 *
 * @author gnosisguild
 *
 */
contract Roles is RolesStorage, Setup, Membership, Authorization, Settlement {
    /// @param _owner Address of the owner
    /// @param _avatar Address of the avatar (e.g. a Gnosis Safe)
    /// @param _target Address of the contract that will call exec function
    constructor(address _owner, address _avatar, address _target) {
        bytes memory initParams = abi.encode(_owner, _avatar, _target);
        setUp(initParams);
    }

    /// @dev Checks whether a module holds an active membership for a role.
    /// @param roleKey Identifier of the role
    /// @param module Address of the module to check
    /// @return True if the module currently has a valid membership for the role
    function isMember(
        bytes32 roleKey,
        address module
    ) external view returns (bool) {
        return _hasActiveMembership(roleKey, module);
    }

    /// @dev Passes a transaction to the modifier using the caller's default role.
    /// @param to Destination address of module transaction
    /// @param value Ether value of module transaction
    /// @param data Data payload of module transaction
    /// @param operation Operation type of module transaction
    /// @notice Can only be called by enabled modules
    function execTransactionFromModule(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation
    ) public override nonReentrant moduleOnly returns (bool success) {
        return
            _execWithRole(
                to,
                value,
                data,
                operation,
                defaultRoles[sentOrSignedByModule()],
                false
            );
    }

    /// @dev Passes a transaction to the modifier using the caller's default role. Expects return data.
    /// @param to Destination address of module transaction
    /// @param value Ether value of module transaction
    /// @param data Data payload of module transaction
    /// @param operation Operation type of module transaction
    /// @notice Can only be called by enabled modules
    function execTransactionFromModuleReturnData(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation
    )
        public
        override
        nonReentrant
        moduleOnly
        returns (bool success, bytes memory returnData)
    {
        return
            _execWithRoleReturnData(
                to,
                value,
                data,
                operation,
                defaultRoles[sentOrSignedByModule()],
                false
            );
    }

    /// @dev Passes a transaction to the modifier assuming the specified role.
    /// @param to Destination address of module transaction
    /// @param value Ether value of module transaction
    /// @param data Data payload of module transaction
    /// @param operation Operation type of module transaction
    /// @param roleKey Identifier of the role to assume for this transaction
    /// @param shouldRevert Should the function revert on inner execution returning success false?
    /// @notice Can only be called by enabled modules
    function execTransactionWithRole(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        bytes32 roleKey,
        bool shouldRevert
    ) public nonReentrant moduleOnly returns (bool success) {
        return _execWithRole(to, value, data, operation, roleKey, shouldRevert);
    }

    /// @dev Relayed variant of execTransactionWithRole. The caller does not
    ///      need to be an enabled module; instead, an enabled module must sign
    ///      the call (EIP-712 over a RoleTx struct).
    /// @param to Destination address of module transaction
    /// @param value Ether value of module transaction
    /// @param data Data payload of module transaction
    /// @param operation Operation type of module transaction
    /// @param roleKey Identifier of the role to assume for this transaction
    /// @param shouldRevert Should the function revert on inner execution returning success false?
    /// @param salt Replay-protection nonce mixed into the signed digest;
    ///        each digest can be consumed only once.
    /// @param signature EIP-712 signature by the module (EOA or ERC-1271)
    function execTransactionWithSignature(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        bytes32 roleKey,
        bool shouldRevert,
        bytes32 salt,
        bytes calldata signature
    )
        external
        nonReentrant
        moduleOnlySigned(
            RoleTx.hashStruct(
                to,
                value,
                data,
                operation,
                roleKey,
                shouldRevert,
                salt
            ),
            signature
        )
        returns (bool success)
    {
        return _execWithRole(to, value, data, operation, roleKey, shouldRevert);
    }

    /*//////////////////////////////////////////////////////////////
                               INTERNALS
    //////////////////////////////////////////////////////////////*/

    function _execWithRole(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        bytes32 roleKey,
        bool shouldRevert
    ) private returns (bool success) {
        (address module, uint256 nextMembership) = _authenticate(roleKey);
        Consumption[] memory consumptions = _authorize(
            roleKey,
            to,
            value,
            data,
            operation
        );
        success = IAvatar(target).execTransactionFromModule(
            to,
            value,
            data,
            operation
        );
        if (shouldRevert && !success) {
            revert ModuleTransactionFailed();
        }
        if (success) {
            _persist(module, roleKey, nextMembership, consumptions);
        }
    }

    function _execWithRoleReturnData(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        bytes32 roleKey,
        bool shouldRevert
    ) private returns (bool success, bytes memory returnData) {
        (address module, uint256 nextMembership) = _authenticate(roleKey);
        Consumption[] memory consumptions = _authorize(
            roleKey,
            to,
            value,
            data,
            operation
        );
        (success, returnData) = IAvatar(target)
            .execTransactionFromModuleReturnData(to, value, data, operation);
        if (shouldRevert && !success) {
            revert ModuleTransactionFailed();
        }
        if (success) {
            _persist(module, roleKey, nextMembership, consumptions);
        }
    }
}
