// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Status} from "./Authorization.sol";

/**
 * @title IRolesError - All custom errors emitted by the Roles Mod
 *
 * @author gnosisguild
 */
interface IRolesError {
    /*//////////////////////////////////////////////////////////////
                            EXECUTION ERRORS
    //////////////////////////////////////////////////////////////*/

    /// Sender is allowed to make this call, but the internal transaction failed
    error ModuleTransactionFailed();

    /// Reentrant call detected
    error Reentrancy();

    /*//////////////////////////////////////////////////////////////
                          AUTHORIZATION ERRORS
    //////////////////////////////////////////////////////////////*/

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
        Status status,
        uint256 violatedNodeIndex,
        uint256 location
    );

    /// No matching permission found for the transaction
    error TransactionNotAllowed(address to, bytes4 selector);

    /// Sending value is not allowed
    error SendNotAllowed(address target);

    /// Delegate call is not allowed
    error DelegateCallNotAllowed(address target);

    /*//////////////////////////////////////////////////////////////
                            DECODING ERRORS
    //////////////////////////////////////////////////////////////*/

    /// Attempted to read beyond calldata bounds
    error CalldataOutOfBounds();

    /*//////////////////////////////////////////////////////////////
                           INTEGRITY ERRORS
    //////////////////////////////////////////////////////////////*/

    /// Root node is invalid or missing
    error UnsuitableRootNode();

    /// Condition tree is not in BFS (breadth-first search) order
    error NotBFS();

    /// Packed condition buffer is malformed (not produced by pack())
    error MalformedConditionBuffer();

    /// Parameter type is unsuitable for the operator at given index
    error UnsuitableParameterType(uint256 index);

    /// Comparison value is unsuitable for the operator at given index
    error UnsuitableCompValue(uint256 index);

    /// Condition count exceeds the packed header's 16-bit field
    error ConditionNodeCountExceedsMax();

    /// Child count exceeds the packed node's 10-bit field
    error ConditionChildCountExceedsMax(uint256 index);

    /// Inlined size exceeds the packed node's 13-bit field
    error ConditionInlinedSizeExceedsMax(uint256 index);

    /// Operator is not supported at given index
    error UnsupportedOperator(uint256 index);

    /// Parent node is unsuitable for the child at given index
    error UnsuitableParent(uint256 index);

    /// Child count is unsuitable for the node at given index
    error UnsuitableChildCount(uint256 index);

    /// Leaf node cannot have children at given index
    error LeafNodeCannotHaveChildren(uint256 index);

    /// Child type tree is unsuitable for the node at given index
    error UnsuitableChildTypeTree(uint256 index);

    /// WithinRatio target must resolve to a Static type
    error WithinRatioTargetNotStatic(uint256 index);

    /// WithinRatio requires at least one ratio (min or max) to be provided
    error WithinRatioNoRatioProvided(uint256 index);

    /// WithinRatio minRatio exceeds maxRatio (range is unsatisfiable)
    error WithinRatioMinExceedsMax(uint256 index);

    /// Allowance decimals exceed maximum of 27
    error AllowanceDecimalsExceedMax(uint256 index);

    /// Slice child must resolve to Static type
    error SliceChildNotStatic(uint256 index);

    /// An operator references a Pluck slot that is not definitely assigned
    error PluckNotVisitedBeforeRef(uint256 index, uint8 pluckIndex);

    /// A Pluck slot is defined more than once in the condition tree
    error DuplicatePluckIndex(uint256 index, uint8 pluckIndex);

    /// address(0) is not allowed
    error ZeroAddressNotAllowed();
}
