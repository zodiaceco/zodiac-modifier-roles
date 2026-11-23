// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Operation} from "@gnosis-guild/zodiac-core/contracts/core/Operation.sol";

/**
 * @title IEvaluator
 * @notice Stateless condition evaluator and serializer invoked via staticcall
 *         by Roles Core.
 */
interface IEvaluator {
    /**
     * @notice Evaluates the condition tree referenced by `scopeConfig` against
     *         the transaction and running allowance consumptions.
     *
     * @param scopeConfig  Packed scope config (options << 160 | pointer).
     * @param to           Destination address of the transaction.
     * @param value        Ether value of the transaction.
     * @param data         Calldata of the transaction.
     * @param operation    Call or DelegateCall.
     * @param consumptions Allowances consumed so far (e.g. in a bundle).
     *
     * @return             Evaluation result: `status == 0` with updated
     *                     consumptions, or a violation code and location.
     */
    function evaluate(
        uint256 scopeConfig,
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        Consumption[] calldata consumptions
    ) external view returns (Result memory);

    /**
     * @notice Validates a flat condition tree and packs it into the Evaluator's
     *         binary representation.
     *
     * @param conditions Condition tree in flat BFS order.
     *
     * @return buffer    Packed condition buffer.
     */
    function pack(
        ConditionFlat[] calldata conditions
    ) external view returns (bytes memory buffer);
}

/**
 * @title IRolesCore
 * @notice Read-only view interface exposed by Roles Core for stateless
 *         Evaluators and custom conditions.
 */
interface IRolesCore {
    function avatar() external view returns (address);

    function accruedAllowance(
        bytes32 allowanceKey
    ) external view returns (uint128 balance, uint64 timestamp);
}

/*//////////////////////////////////////////////////////////////
                             TYPES
//////////////////////////////////////////////////////////////*/

struct Consumption {
    bytes32 allowanceKey;
    uint128 balance;
    uint128 consumed;
    uint64 timestamp;
}

/// @dev Flattened condition tree node in BFS order (ABI does not support
///      recursive structs). `paramType` and `operator` are raw uint8 codes
///      interpreted by the Evaluator.
struct ConditionFlat {
    uint16 parent;
    uint8 paramType;
    uint8 operator;
    bytes compValue;
}

/// @dev Evaluation outcome returned by an Evaluator.
///      - On pass (`status == 0`): `consumptions` holds the updated allowance
///        consumptions.
///      - On failure (`status != 0`): `status` is an Evaluator-defined
///        violation code, with `violatedNodeIndex` and `calldataOffset`
///        locating the failure (`consumptions` is empty).
struct Result {
    uint8 status;
    uint256 violatedNodeIndex;
    uint256 calldataOffset;
    Consumption[] consumptions;
}
