// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../common/AllowanceConsumer.sol";
import "./serialize/ConditionStorer.sol";
import "./Storage.sol";

/**
 * @title  Setup
 * @notice Owner configuration of roles, permissions, allowances, and unwrappers.
 *
 * @dev    Permission lookup
 *         ─────────────────
 *         A permission is a `scopeConfig` entry:
 *         - `ExecutionOptions`: whether the call may send value, delegatecall
 *         - condition tree: pointer to the packed tree, stored as contract code
 *
 *         Its key has three components: a target address, a selector and
 *         padding. They give the entry one of three scopes:
 *
 *         ┌─────────────────┬──────────┬──────────┬──────────┐
 *         │      Scope      │ bytes 20 │ bytes 4  │ bytes 8  │
 *         ├─────────────────┼──────────┼──────────┼──────────┤
 *         │ target          │ address  │ 0xFF..FF │ 0xFF..FF │
 *         │ function        │ address  │ selector │ 0x00..00 │
 *         │ global function │ 0x00..00 │ selector │ 0x00..00 │
 *         └─────────────────┴──────────┴──────────┴──────────┘
 *
 *         For a call to a target, the `clearance[target]` config sets which
 *         entries are checked, in order. The first one found governs the
 *         call. If none is found, the call reverts with
 *         `TransactionNotAllowed`.
 *
 *         None (the default): `target` has no rule of its own.
 *           1. global function entry for the selector
 *           2. if none matches, revert: the call is unauthorized
 *
 *         Target: one rule covers every call to `target`.
 *           1. target entry
 *           2. if none matches, revert: the call is unauthorized
 *
 *         Function: each function of `target` has its own rule.
 *           1. function entry for the selector
 *           2. global function entry for the selector
 *           3. if none matches, revert: the call is unauthorized
 *
 *         A global function entry allows one selector on any target. It
 *         never permits sending value or delegatecall, and is skipped for
 *         empty calldata.
 *
 *         Clearance and entries are written independently:
 *         - `allowTarget` sets Target and writes the target entry.
 *         - `scopeTarget` sets Function; `revokeTarget` resets to None.
 *         - `allowFunction` and `revokeFunction` write and delete a function
 *           entry, which applies only under Function.
 *         Changing the clearance deletes no entries: function entries
 *         written earlier apply again once the target is scoped.
 *
 *         Packed words
 *         ────────────
 *         members[module]     start (64) | end (64) | usesLeft (128)
 *         scopeConfig[key]    unused (94) | options (2) | pointer (160)
 *
 *         `pointer` is the address holding the packed condition tree. A
 *         zero `scopeConfig` means no entry.
 *
 *         Validated vs. pre-packed setters
 *         ────────────────────────────────
 *         Validated: `allowTarget`, `allowFunction`, `allowFunctionGlobally`.
 *         Take a `ConditionFlat[]` tree, validate it (`Integrity`) and pack
 *         it on-chain, so the stored buffer is well-formed.
 *
 *         Pre-packed: `allowTargetPacked`, `allowFunctionPacked`,
 *         `allowFunctionGloballyPacked`. Store a buffer as-is, with no
 *         validation: the caller is responsible for it. Build one off-chain
 *         with the SDK, or with an eth_call to `packConditions`.
 */
abstract contract Setup is RolesStorage {
    /*//////////////////////////////////////////////////////////////
                            INITIALIZATION
    //////////////////////////////////////////////////////////////*/

    function setUp(
        bytes memory initParams
    ) public virtual override initializer {
        (address _owner, address _avatar, address _target) = abi.decode(
            initParams,
            (address, address, address)
        );
        _transferOwnership(_owner);
        avatar = _avatar;
        target = _target;

        setupModules();

        emit RolesModSetup(msg.sender, _owner, _avatar, _target, VERSION);
    }

    /*//////////////////////////////////////////////////////////////
                           ROLE MEMBERSHIP
    //////////////////////////////////////////////////////////////*/

    /// @dev Grants a role to a module with optional session parameters.
    /// @param module Module to grant the role to.
    /// @param roleKey Role to grant.
    /// @param startTimestamp Start timestamp (0 = immediately valid).
    /// @param endTimestamp End timestamp (0 = never expires).
    /// @param usesLeft Number of uses (0 = unlimited).
    function grantRole(
        address module,
        bytes32 roleKey,
        uint64 startTimestamp,
        uint64 endTimestamp,
        uint128 usesLeft
    ) public onlyOwner {
        endTimestamp = endTimestamp != 0 ? endTimestamp : type(uint64).max;
        usesLeft = usesLeft != 0 ? usesLeft : type(uint128).max;
        roles[roleKey].members[module] =
            (uint256(startTimestamp) << 192) |
            (uint256(endTimestamp) << 128) |
            uint256(usesLeft);
        if (!isModuleEnabled(module)) {
            enableModule(module);
        }
        emit GrantRole(roleKey, module, startTimestamp, endTimestamp, usesLeft);
    }

    /// @dev Revokes a role from a module.
    /// @param module Module to revoke the role from.
    /// @param roleKey Role to revoke.
    function revokeRole(address module, bytes32 roleKey) public onlyOwner {
        delete roles[roleKey].members[module];
        emit RevokeRole(roleKey, module);
    }

    /// @dev Allows a module to renounce its own role.
    /// @param roleKey Role to renounce.
    function renounceRole(bytes32 roleKey) external {
        delete roles[roleKey].members[msg.sender];
        emit RevokeRole(roleKey, msg.sender);
    }

    /// @dev Batch assigns roles to a module.
    /// @param module Module to assign roles to.
    /// @param roleKeys Roles to assign.
    /// @param memberOf true to grant, false to revoke.
    function assignRoles(
        address module,
        bytes32[] calldata roleKeys,
        bool[] calldata memberOf
    ) external onlyOwner {
        for (uint256 i; i < roleKeys.length; ++i) {
            bytes32 key = roleKeys[i];
            if (memberOf[i]) {
                grantRole(module, key, 0, 0, 0);
            } else {
                revokeRole(module, key);
            }
        }
    }

    /// @dev Sets the default role used for a module if it calls
    ///      execTransactionFromModule() or execTransactionFromModuleReturnData().
    /// @param module Address of the module on which to set default role.
    /// @param roleKey Role to be set as default.
    function setDefaultRole(
        address module,
        bytes32 roleKey
    ) external onlyOwner {
        defaultRoles[module] = roleKey;
        emit SetDefaultRole(module, roleKey);
    }

    /*//////////////////////////////////////////////////////////////
                         TARGET PERMISSIONS
    //////////////////////////////////////////////////////////////*/

    /// @dev Allows transactions to a target address, restricted by a
    ///      target-wide condition: the same condition tree governs every
    ///      call to the target, regardless of selector.
    ///
    ///      Sets Clearance.Target and writes the target entry.
    ///
    ///      Conditions are validated and packed on-chain; use
    ///      allowTargetPacked() for a pre-packed buffer.
    /// @param roleKey identifier of the role to be modified.
    /// @param targetAddress Destination address of transaction.
    /// @param conditions Condition tree in flat BFS order. Empty array means
    ///        no payload restrictions (pass-through).
    /// @param options designates if a transaction can send ether and/or delegatecall to target.
    function allowTarget(
        bytes32 roleKey,
        address targetAddress,
        ConditionFlat[] memory conditions,
        ExecutionOptions options
    ) external {
        allowTargetPacked(
            roleKey,
            targetAddress,
            packConditions(conditions),
            options
        );
    }

    /// @dev Allows transactions to a target address using a pre-packed
    ///      condition buffer. Same effect as allowTarget(), but skips
    ///      on-chain validation - see the contract-level note for the tradeoff.
    /// @param roleKey identifier of the role to be modified.
    /// @param targetAddress Destination address of transaction.
    /// @param packedConditions Pre-packed condition buffer. Empty bytes means
    ///        no payload restrictions (a single Pass condition is stored).
    /// @param options designates if a transaction can send ether and/or delegatecall to target.
    function allowTargetPacked(
        bytes32 roleKey,
        address targetAddress,
        bytes memory packedConditions,
        ExecutionOptions options
    ) public onlyOwner {
        _requireNonZeroAddress(targetAddress);
        bytes32 key = bytes32(bytes20(targetAddress)) | (~bytes32(0) >> 160);

        roles[roleKey].clearance[targetAddress] = Clearance.Target;
        roles[roleKey].scopeConfig[key] = ConditionStorer.store(
            _conditionsOrPass(packedConditions),
            options
        );

        emit AllowTarget(roleKey, targetAddress, packedConditions, options);
    }

    /// @dev Designates only specific functions can be called.
    /// @param roleKey identifier of the role to be modified.
    /// @param targetAddress Destination address of transaction.
    function scopeTarget(
        bytes32 roleKey,
        address targetAddress
    ) external onlyOwner {
        _requireNonZeroAddress(targetAddress);
        roles[roleKey].clearance[targetAddress] = Clearance.Function;
        emit ScopeTarget(roleKey, targetAddress);
    }

    /// @dev Resets Clearance to None: only a global function entry can still
    ///      authorize calls to this target. Deletes no entries.
    /// @param roleKey identifier of the role to be modified.
    /// @param targetAddress Destination address of transaction.
    function revokeTarget(
        bytes32 roleKey,
        address targetAddress
    ) external onlyOwner {
        _requireNonZeroAddress(targetAddress);
        delete roles[roleKey].clearance[targetAddress];
        emit RevokeTarget(roleKey, targetAddress);
    }

    /*//////////////////////////////////////////////////////////////
                        FUNCTION PERMISSIONS
    //////////////////////////////////////////////////////////////*/

    /// @dev Allows a single function on a target address, restricted by
    ///      validated conditions. Writes a function entry, which takes effect
    ///      only while the target is scoped (Clearance.Function, see
    ///      scopeTarget). Conditions are validated and packed on-chain; use
    ///      allowFunctionPacked() for a pre-packed buffer.
    /// @param roleKey identifier of the role to be modified.
    /// @param targetAddress Destination address of transaction.
    /// @param selector 4 byte function selector.
    /// @param conditions Condition tree in flat BFS order. Empty array means
    ///        no payload restrictions (pass-through).
    /// @param options designates if a transaction can send ether and/or delegatecall to target.
    function allowFunction(
        bytes32 roleKey,
        address targetAddress,
        bytes4 selector,
        ConditionFlat[] memory conditions,
        ExecutionOptions options
    ) external {
        allowFunctionPacked(
            roleKey,
            targetAddress,
            selector,
            packConditions(conditions),
            options
        );
    }

    /// @dev Allows a single function on a target address using pre-packed
    ///      conditions. Same effect as allowFunction(), but skips on-chain
    ///      validation - see the contract-level note for the tradeoff.
    /// @param roleKey identifier of the role to be modified.
    /// @param targetAddress Destination address of transaction.
    /// @param selector 4 byte function selector.
    /// @param packedConditions Pre-packed condition buffer. Empty bytes means
    ///        no payload restrictions (a single Pass condition is stored).
    /// @param options designates if a transaction can send ether and/or delegatecall to target.
    function allowFunctionPacked(
        bytes32 roleKey,
        address targetAddress,
        bytes4 selector,
        bytes memory packedConditions,
        ExecutionOptions options
    ) public onlyOwner {
        _requireNonZeroAddress(targetAddress);
        roles[roleKey].scopeConfig[
            _key(targetAddress, selector)
        ] = ConditionStorer.store(_conditionsOrPass(packedConditions), options);

        emit AllowFunction(
            roleKey,
            targetAddress,
            selector,
            packedConditions,
            options
        );
    }

    /// @dev Writes a global function entry: allows a function selector on
    ///      all targets, restricted by validated conditions. Always enforces
    ///      no send and no delegatecall (ExecutionOptions.None). Consulted
    ///      only when no target or function entry matches, and never for
    ///      empty calldata. Conditions are validated and packed on-chain; use
    ///      allowFunctionGloballyPacked() for a pre-packed buffer.
    /// @param roleKey identifier of the role to be modified.
    /// @param selector 4 byte function selector.
    /// @param conditions Condition tree in flat BFS order. Empty array means
    ///        no payload restrictions (pass-through).
    function allowFunctionGlobally(
        bytes32 roleKey,
        bytes4 selector,
        ConditionFlat[] memory conditions
    ) external {
        allowFunctionGloballyPacked(
            roleKey,
            selector,
            packConditions(conditions)
        );
    }

    /// @dev Allows a function selector on all targets using pre-packed
    ///      conditions. Same effect as allowFunctionGlobally(), but skips
    ///      on-chain validation - see the contract-level note for the tradeoff.
    /// @param roleKey identifier of the role to be modified.
    /// @param selector 4 byte function selector.
    /// @param packedConditions Pre-packed condition buffer. Empty bytes means
    ///        no payload restrictions (a single Pass condition is stored).
    function allowFunctionGloballyPacked(
        bytes32 roleKey,
        bytes4 selector,
        bytes memory packedConditions
    ) public onlyOwner {
        roles[roleKey].scopeConfig[_key(address(0), selector)] = ConditionStorer
            .store(_conditionsOrPass(packedConditions), ExecutionOptions.None);

        emit AllowFunctionGlobally(roleKey, selector, packedConditions);
    }

    /// @dev Deletes the function entry for a selector on a target.
    /// @param roleKey identifier of the role to be modified.
    /// @param targetAddress Destination address of transaction.
    /// @param selector 4 byte function selector.
    function revokeFunction(
        bytes32 roleKey,
        address targetAddress,
        bytes4 selector
    ) external onlyOwner {
        _requireNonZeroAddress(targetAddress);
        delete roles[roleKey].scopeConfig[_key(targetAddress, selector)];
        emit RevokeFunction(roleKey, targetAddress, selector);
    }

    /// @dev Deletes the global function entry for a selector.
    /// @param roleKey identifier of the role to be modified.
    /// @param selector 4 byte function selector.
    function revokeFunctionGlobally(
        bytes32 roleKey,
        bytes4 selector
    ) external onlyOwner {
        delete roles[roleKey].scopeConfig[_key(address(0), selector)];
        emit RevokeFunctionGlobally(roleKey, selector);
    }

    /*//////////////////////////////////////////////////////////////
                             ALLOWANCES
    //////////////////////////////////////////////////////////////*/

    function setAllowance(
        bytes32 key,
        uint128 balance,
        uint128 maxRefill,
        uint128 refill,
        uint64 period,
        uint64 timestamp
    ) external onlyOwner {
        maxRefill = maxRefill != 0 ? maxRefill : type(uint128).max;
        timestamp = timestamp != 0 ? timestamp : uint64(block.timestamp);

        allowances[key] = Allowance({
            refill: refill,
            maxRefill: maxRefill,
            period: period,
            timestamp: timestamp,
            balance: balance
        });
        emit SetAllowance(key, balance, maxRefill, refill, period, timestamp);
    }

    /// @dev Updates only the refill parameters of an existing allowance, preserving balance and timestamp.
    /// @param key The allowance key.
    /// @param maxRefill Cap at which refilling stops. Pass 0 to set to max uint128.
    /// @param refill Amount added to balance each period.
    /// @param period Refill interval in seconds.
    function updateAllowance(
        bytes32 key,
        uint128 maxRefill,
        uint128 refill,
        uint64 period
    ) external onlyOwner {
        maxRefill = maxRefill != 0 ? maxRefill : type(uint128).max;
        uint64 timestamp = allowances[key].timestamp;
        uint128 balance = allowances[key].balance;

        allowances[key].refill = refill;
        allowances[key].maxRefill = maxRefill;
        allowances[key].period = period;

        emit SetAllowance(key, balance, maxRefill, refill, period, timestamp);
    }

    /// @dev Returns the accrued allowance balance at current block.timestamp.
    /// @param allowanceKey The allowance key.
    /// @return balance The accrued balance.
    /// @return timestamp The timestamp of the last accrual point.
    function accruedAllowance(
        bytes32 allowanceKey
    ) external view returns (uint128 balance, uint64 timestamp) {
        return AllowanceConsumer.accrue(allowanceKey, uint64(block.timestamp));
    }

    /*//////////////////////////////////////////////////////////////
                              ADAPTERS
    //////////////////////////////////////////////////////////////*/

    function setTransactionUnwrapper(
        address to,
        bytes4 selector,
        address adapter
    ) external onlyOwner {
        unwrappers[bytes32(bytes20(to)) | (bytes32(selector) >> 160)] = adapter;
        emit SetUnwrapAdapter(to, selector, adapter);
    }

    /*//////////////////////////////////////////////////////////////
                               HELPERS
    //////////////////////////////////////////////////////////////*/

    /// @dev Read-only entrypoint for packing conditions: permission authors
    ///      can eth_call this to validate and pack, then pass the buffer to
    ///      a *Packed setter. An empty array packs to empty bytes - no
    ///      payload restrictions (pass-through).
    /// @param conditions The conditions to pack, in flat BFS order.
    /// @return buffer The packed condition buffer.
    function packConditions(
        ConditionFlat[] memory conditions
    ) public pure returns (bytes memory buffer) {
        if (conditions.length > 0) {
            buffer = ConditionStorer.pack(conditions);
        }
    }

    /*//////////////////////////////////////////////////////////////
                               INTERNALS
    //////////////////////////////////////////////////////////////*/

    /// @dev If buffer is empty, returns packed single Pass condition;
    ///      otherwise returns the buffer unchanged.
    function _conditionsOrPass(
        bytes memory buffer
    ) private pure returns (bytes memory) {
        if (buffer.length == 0) {
            return ConditionStorer.pack(new ConditionFlat[](1));
        }
        return buffer;
    }

    function _requireNonZeroAddress(address targetAddress) private pure {
        if (targetAddress == address(0)) revert ZeroAddressNotAllowed();
    }
}
