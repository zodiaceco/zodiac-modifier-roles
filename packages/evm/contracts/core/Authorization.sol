// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "./Storage.sol";

import "../IEvaluator.sol";
import "../periphery/interfaces/ITransactionUnwrapper.sol";

/**
 * @title   Authorization
 *
 * @notice Authorizes transactions by evaluating role permissions and condition
 *         trees.
 *
 * @dev    The authorization follows three steps:
 *         1. Scope Resolution: Resolves the permission configuration
 *         2. Execution Options: Checks for value transfer and tx operation
 *         3. Payload Validation: Evaluates condition trees against tx data
 *
 *         Transaction bundles are supported via adapter-based unwrapping.
 */
abstract contract Authorization is RolesStorage {
    function _authorize(
        bytes32 roleKey,
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation
    ) internal view returns (Consumption[] memory consumptions) {
        address adapter = unwrappers[_key(to, bytes4(data))];
        if (adapter == address(0)) {
            return
                _transaction(
                    roleKey,
                    data,
                    consumptions,
                    Transaction(to, value, operation)
                );
        }

        /*
         * Transaction Bundle
         */
        try
            ITransactionUnwrapper(adapter).unwrap(to, value, data, operation)
        returns (UnwrappedTransaction[] memory unwrapped) {
            for (uint256 i; i < unwrapped.length; ++i) {
                UnwrappedTransaction memory entry = unwrapped[i];
                consumptions = _transaction(
                    roleKey,
                    data[entry.dataLocation:entry.dataLocation +
                        entry.dataSize],
                    consumptions,
                    Transaction(entry.to, entry.value, entry.operation)
                );
            }
        } catch {
            revert MalformedMultiEntrypoint();
        }
    }

    /// @dev Inspects a transaction and authorizes based on role permissions.
    function _transaction(
        bytes32 roleKey,
        bytes calldata data,
        Consumption[] memory consumptions,
        Transaction memory transaction
    ) private view returns (Consumption[] memory) {
        Role storage role = roles[roleKey];

        if (data.length != 0 && data.length < 4) {
            revert FunctionSignatureTooShort();
        }

        /*
         * Resolve the scopeConfig governing this transaction.
         *
         * Clearance records how the owner scoped the target:
         *   Target:   whole contract allowed - any calldata, even empty
         *   Function: only individually allowed selectors
         *   None:     not scoped - only a global function entry can authorize
         *
         * A scopeConfig key has three components: a target address, a
         * selector and padding. They give the entry one of three scopes:
         *
         * ┌─────────────────┬──────────┬──────────┬──────────┐
         * │      Scope      │ bytes 20 │ bytes 4  │ bytes 8  │
         * ├─────────────────┼──────────┼──────────┼──────────┤
         * │ target          │ address  │ 0xFF..FF │ 0xFF..FF │
         * │ function        │ address  │ selector │ 0x00..00 │
         * │ global function │ 0x00..00 │ selector │ 0x00..00 │
         * └─────────────────┴──────────┴──────────┴──────────┘
         *
         * A target entry covers any calldata on the target, a global function
         * entry one selector on any target.
         *
         * A function entry can never collide with a target entry: it always
         * has 8 zero bytes where a target entry has 0xFF.
         */
        Clearance clearance = role.clearance[transaction.to];

        /*
         * Lookup 1 of 2: destination-specific entry.
         * Destination rules take precedence over global rules, so this is
         * consulted first.
         *
         * Clearance.None falls through: only a global function entry can
         * authorize.
         */
        uint256 scopeConfig;
        if (clearance == Clearance.Function) {
            scopeConfig = role.scopeConfig[
                bytes32(bytes20(transaction.to)) |
                    (bytes32(bytes4(data)) >> 160)
            ];
        } else if (clearance == Clearance.Target) {
            scopeConfig = role.scopeConfig[
                bytes32(bytes20(transaction.to)) | (~bytes32(0) >> 160)
            ];
        }

        /*
         * Lookup 2 of 2: global function entry. Same layout with the address
         * zeroed: selector allowed on any target (write side:
         * allowFunctionGlobally).
         * Requires a selector, so empty-calldata calls never resolve here.
         */
        if (scopeConfig == 0 && data.length != 0) {
            scopeConfig = role.scopeConfig[bytes32(bytes4(data)) >> 160];
        }

        /*
         * scopeConfig == 0 means no permission configured.
         */
        if (scopeConfig == 0) {
            revert TransactionNotAllowed(transaction.to, bytes4(data));
        }

        /*
         * Enforce ExecutionOptions packed in the high bits of scopeConfig.
         * The enum values double as bit flags:
         *
         *   None = 0 (00)   Send = 1 (01)
         *   Both = 3 (11)   DelegateCall = 2 (10)
         *
         *   bit 0 set -> transaction may carry ether
         *   bit 1 set -> transaction may delegatecall
         */
        {
            uint256 options = scopeConfig >> 160;
            // can Send ?
            if (options & 1 == 0 && transaction.value > 0) {
                revert SendNotAllowed(transaction.to);
            }
            // can DelegateCall ?
            if (
                options & 2 == 0 &&
                transaction.operation == Operation.DelegateCall
            ) {
                revert DelegateCallNotAllowed(transaction.to);
            }
        }

        /*
         * Delegate condition loading & evaluation to the stateless Evaluator
         */
        address _evaluator = evaluator;
        if (_evaluator.code.length == 0) {
            revert EvaluatorNotAContract(_evaluator);
        }

        Result memory result = IEvaluator(_evaluator).evaluate(
            scopeConfig,
            transaction.to,
            transaction.value,
            data,
            transaction.operation,
            consumptions
        );

        if (result.status != 0) {
            revert ConditionViolation(
                result.status,
                result.violatedNodeIndex,
                result.calldataOffset
            );
        }

        return result.consumptions;
    }
}
