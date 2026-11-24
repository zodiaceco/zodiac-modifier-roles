// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "./core/Authorization.sol";
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
contract Roles is RolesStorage, Setup, Authorization, Settlement {
    /// @param _owner Address of the owner
    /// @param _avatar Address of the avatar (e.g. a Gnosis Safe)
    /// @param _target Address of the contract that will call exec function
    /// @param _evaluator Address of the stateless condition evaluator contract
    constructor(
        address _owner,
        address _avatar,
        address _target,
        address _evaluator
    ) {
        bytes memory initParams = abi.encode(
            _owner,
            _avatar,
            _target,
            _evaluator
        );
        setUp(initParams);
    }

    /*//////////////////////////////////////////////////////////////
                      STANDARD EXECUTION (IAvatar)
    //////////////////////////////////////////////////////////////*/

    /// @dev Passes a transaction to the modifier using the caller's default
    ///      role. Returns false, without reverting, if the inner execution
    ///      fails.
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
        (success, ) = _exec(to, value, data, operation, _defaultRole());
    }

    /// @dev Passes a transaction to the modifier using the caller's default
    ///      role. Returns false and the revert data, without reverting, if
    ///      the inner execution fails.
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
        return _exec(to, value, data, operation, _defaultRole());
    }

    /*//////////////////////////////////////////////////////////////
                           ROLE EXECUTION
    //////////////////////////////////////////////////////////////*/

    /// @dev Passes a transaction to the modifier assuming the specified role.
    ///      Reverts with ModuleTransactionFailed(returnData) if the inner
    ///      execution fails.
    /// @param to Destination address of module transaction
    /// @param value Ether value of module transaction
    /// @param data Data payload of module transaction
    /// @param operation Operation type of module transaction
    /// @param roleKey Identifier of the role to assume for this transaction
    /// @return returnData Data returned by the inner execution
    /// @notice Can only be called by enabled modules
    function execTransactionWithRole(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        bytes32 roleKey
    ) external nonReentrant moduleOnly returns (bytes memory returnData) {
        return _execStrict(to, value, data, operation, roleKey);
    }

    /// @dev Relayed variant of execTransactionWithRole. The caller does not
    ///      need to be an enabled module; instead, an enabled module must sign
    ///      the transaction (EIP-712 over RoleTx, EOA or ERC-1271).
    ///      Reverts with ModuleTransactionFailed(returnData) if the inner
    ///      execution fails; the revert leaves the signature unconsumed, so
    ///      it stays valid until it executes, is invalidated or expires.
    /// @param roleTx The signed transaction
    /// @param signature Signature by the module over the EIP-712 digest of roleTx
    /// @return returnData Data returned by the inner execution
    function execTransactionWithRoleSigned(
        RoleTx calldata roleTx,
        bytes calldata signature
    )
        external
        nonReentrant
        moduleOnlySigned(RoleTxLib.hashStruct(roleTx), signature)
        returns (bytes memory returnData)
    {
        if (block.timestamp > roleTx.deadline) {
            revert SignatureExpired();
        }
        return
            _execStrict(
                roleTx.to,
                roleTx.value,
                roleTx.data,
                roleTx.operation,
                roleTx.roleKey
            );
    }

    /*//////////////////////////////////////////////////////////////
                               INTERNALS
    //////////////////////////////////////////////////////////////*/

    /// @dev Identifies the module that sent or signed the current call (set
    ///      by moduleOnly / moduleOnlySigned at the entry points) and verifies
    ///      its membership of `roleKey`.
    function _authenticate(
        bytes32 roleKey
    ) private view returns (address module) {
        // Never authorize the zero role
        if (roleKey == 0) {
            revert NoMembership();
        }

        module = sentOrSignedByModule();

        uint256 membership = roles[roleKey].members[module];
        if (membership == 0) {
            revert NoMembership();
        }
        if (block.timestamp < uint64(membership >> 192)) {
            revert MembershipNotYetValid();
        }
        if (block.timestamp > uint64(membership >> 128)) {
            revert MembershipExpired();
        }
    }

    /// @dev Does not revert if the inner execution fails, for IAvatar
    ///      compatibility.
    function _exec(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        bytes32 roleKey
    ) private returns (bool success, bytes memory returnData) {
        address module = _authenticate(roleKey);
        Consumption[] memory consumptions = _authorize(
            roleKey,
            to,
            value,
            data,
            operation
        );
        (success, returnData) = IAvatar(target)
            .execTransactionFromModuleReturnData(to, value, data, operation);
        if (success) {
            _settle(module, roleKey, consumptions);
        }
    }

    /// @dev Reverts if the inner execution fails.
    function _execStrict(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        bytes32 roleKey
    ) private returns (bytes memory returnData) {
        bool success;
        (success, returnData) = _exec(to, value, data, operation, roleKey);
        if (!success) {
            revert ModuleTransactionFailed(returnData);
        }
    }

    function _defaultRole() private view returns (bytes32 roleKey) {
        roleKey = defaultRoles[sentOrSignedByModule()];
        if (roleKey == 0) {
            revert NoDefaultRole();
        }
    }
}
