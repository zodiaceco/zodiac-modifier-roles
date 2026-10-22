// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../common/AllowanceConsumer.sol";
import "./serialize/ConditionStorer.sol";
import "./Storage.sol";

import {Clearance} from "../types/Permission.sol";

/*
 * Permission Model
 *
 * Role
 *  │
 *  ├─ members ───────────────────────► who can use this role
 *  │
 *  ├─ targets (address → Clearance)
 *  │   │
 *  │   ├─ Clearance.None ────────────► no target rule (default) - only a
 *  │   │                               global entry can authorize
 *  │   │
 *  │   ├─ Clearance.Target ──────────► all functions allowed, subject to
 *  │   │                               the target entry below (wildcard)
 *  │   │
 *  │   └─ Clearance.Function ────────► only functions with a function
 *  │                                   entry below are allowed
 *  │
 *  └─ scopeConfig (key → ExecutionOptions + condition tree)
 *      │
 *      │   Key: [20 bytes: address][8 bytes][4 bytes]
 *      │   ├─ Function entry: address  | 0x00..00 | selector  one selector on one address
 *      │   ├─ Target entry:   address  |        0xFF..FF      any calldata on one address
 *      │   └─ Global entry:   0x00..00 | 0x00..00 | selector  one selector on any address
 *      │
 *      ├─ no matching entry ─────────► blocked (TransactionNotAllowed)
 *      │
 *      └─ matching entry ────────────► allowed, subject to ExecutionOptions
 *                                      (send/delegatecall flags) and the
 *                                      condition tree
 *
 * Resolution: the destination-specific entry (function or target, per
 * Clearance) is consulted first - destination rules take precedence over
 * global rules. If no destination-specific entry matches, the global entry
 * applies. A global entry keys on the selector, so calls with empty calldata
 * never resolve globally.
 *
 * Allowances (separate storage, referenced by conditions)
 */

/**
 * @title Setup - Configuration and setup functions for Zodiac Roles Mod.
 *
 * @dev Permission setters come in two flavors:
 *
 *      - Validated (allowTarget, allowFunction, allowFunctionGlobally):
 *        take a ConditionFlat[] tree, then validate (Integrity) and pack it
 *        on-chain. Costs more setup gas, but the stored buffer is guaranteed
 *        well-formed.
 *      - Packed (allowTargetPacked, allowFunctionPacked,
 *        allowFunctionGloballyPacked): take a pre-packed condition buffer
 *        and store it as-is, skipping on-chain validation. An escape hatch
 *        for large condition trees, where packing on-chain can be costly.
 *
 *      To produce a buffer, call the read-only packConditions() off-chain
 *      (eth_call): validation runs offchain, only the storage write is paid.
 *
 * @author  gnosisguild
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
    ///      Sets Clearance.Target.
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

    /// @dev Removes the target-level rule: resets Clearance to None, so only
    ///      a global entry can still authorize calls to this target.
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

    /// @dev Allows a function selector on all targets, restricted by validated
    ///      conditions. Always enforces no send and no delegatecall
    ///      (ExecutionOptions.None). Consulted only when no destination-
    ///      specific entry matches, and only for calls carrying a selector - calls with
    ///      empty calldata never resolve via a global entry. Conditions are
    ///      validated and packed on-chain; use allowFunctionGloballyPacked()
    ///      for a pre-packed buffer.
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

    /// @dev Removes a function permission for a target.
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

    /// @dev Removes a globally allowed function permission.
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
