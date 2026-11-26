// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

/**
 * @title ICoreError - Custom errors emitted by Roles Core
 */
interface ICoreError {
    /*//////////////////////////////////////////////////////////////
                            EXECUTION ERRORS
    //////////////////////////////////////////////////////////////*/

    /// Sender is allowed to make this call, but the internal transaction
    /// failed. Carries the data it reverted with.
    error ModuleTransactionFailed(bytes returnData);

    /// The signed transaction's deadline has passed
    error SignatureExpired();

    /// Reentrant call detected
    error Reentrancy();

    /*//////////////////////////////////////////////////////////////
                          AUTHORIZATION ERRORS
    //////////////////////////////////////////////////////////////*/

    /// Sender has no default role set
    error NoDefaultRole();

    /// Sender is not a member of the role
    error NoMembership();

    /// Membership is not yet valid (before start timestamp)
    error MembershipNotYetValid();

    /// Membership has expired (after end timestamp)
    error MembershipExpired();

    /// Function signature too short
    error FunctionSignatureTooShort();

    /// Calldata unwrapping failed
    error MalformedMultiEntrypoint();

    /// Authorization check failed with violation information
    error ConditionViolation(
        uint8 status,
        uint256 violatedNodeIndex,
        uint256 calldataOffset
    );

    /// Settlement attempted to consume more than the accrued allowance balance
    error AllowanceExceeded(bytes32 allowanceKey);

    /// No matching permission found for the transaction
    error TransactionNotAllowed(address to, bytes4 selector);

    /// Sending value is not allowed
    error SendNotAllowed(address target);

    /// Delegate call is not allowed
    error DelegateCallNotAllowed(address target);

    /// Configured evaluator has no deployed code
    error EvaluatorNotAContract(address evaluator);

    /*//////////////////////////////////////////////////////////////
                              SETUP ERRORS
    //////////////////////////////////////////////////////////////*/

    /// address(0) is not allowed
    error ZeroAddressNotAllowed();

    /// Deploying the pointer contract for a packed condition buffer failed
    error ExtCodeWriteFailed();
}
