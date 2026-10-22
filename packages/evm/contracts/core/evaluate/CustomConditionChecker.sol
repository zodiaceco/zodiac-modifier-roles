// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../common/AllowanceConsumer.sol";
import "../../periphery/interfaces/ICustomCondition.sol";

import "../../types/Types.sol";

/**
 * @title CustomConditionChecker
 * @notice Validates transactions against external custom condition adapters.
 *
 * @dev Safely invokes ICustomCondition.check via staticcall. A passing adapter
 *      may return allowance consumptions, which are recorded in the running
 *      consumption list via AllowanceConsumer (copy-on-write: the caller's
 *      list is never mutated).
 *
 *   | Scenario              | staticcall Result      | Behavior                      | Status                          |
 *   |-----------------------|------------------------|-------------------------------|---------------------------------|
 *   | No code at address    | (true, "")             | extcodesize == 0              | CustomConditionNotAContract     |
 *   | Wrong interface       | (false, "")            | staticcall fails              | CustomConditionReverted         |
 *   | Function reverts      | (false, <error data>)  | staticcall fails              | CustomConditionReverted         |
 *   | Returns wrong type    | (true, <invalid ABI>)  | Manual validation fails       | CustomConditionInvalidResult    |
 *   | Returns false         | (true, <success>)      | Adapter rejects the condition | CustomConditionViolation        |
 *   | Exceeds allowance     | (true, <consumptions>) | Core rejects consumption      | AllowanceExceeded               |
 *
 * @author gnosisguild
 */
library CustomConditionChecker {
    /**
     * @notice Evaluates a custom condition against an external adapter.
     * @param compValue Packed config: adapter address (20 bytes) + optional extra data
     * @param to Target address of the transaction
     * @param value ETH value of the transaction
     * @param data Calldata of the transaction
     * @param operation Call or DelegateCall
     * @param location Byte offset into calldata
     * @param size Byte size of the payload at location
     * @param consumptions Running allowance consumption list
     * @param pluckedValues Array of previously plucked values
     * @return status Ok if condition passes, error status otherwise
     * @return The updated consumption list when the adapter passes
     */
    function check(
        bytes calldata compValue,
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        uint256 location,
        uint256 size,
        Consumption[] memory consumptions,
        bytes32[] calldata pluckedValues
    ) external view returns (Status, Consumption[] memory) {
        address adapter = address(bytes20(compValue));

        if (adapter.code.length == 0) {
            return (Status.CustomConditionNotAContract, consumptions);
        }

        (bool success, bytes memory result) = adapter.staticcall(
            abi.encodeCall(
                ICustomCondition.check,
                (
                    to,
                    value,
                    data,
                    operation,
                    location,
                    size,
                    compValue[20:],
                    pluckedValues
                )
            )
        );
        if (!success) {
            return (Status.CustomConditionReverted, consumptions);
        }

        (
            Status status,
            AllowanceConsumption[] memory usedConsumptions
        ) = _parseResult(result);
        if (status != Status.Ok) {
            return (status, consumptions);
        }

        return _applyConsumptions(consumptions, usedConsumptions);
    }

    /**
     * @dev Validates and decodes the adapter result, which must be canonical
     *      ABI for (bool success, AllowanceConsumption[] consumptions):
     *
     *        word 0: success (0 or 1)
     *        word 1: offset of the consumptions array (always 0x40)
     *        word 2: array length N, then N {allowanceKey, amount} pairs
     *
     *      Validated by hand because abi.decode reverts on malformed data,
     *      while the adapter's failure must surface as a status.
     *
     * @return status Ok when the adapter passes, error status otherwise
     * @return consumptions Consumptions to apply (empty unless Ok)
     */
    function _parseResult(
        bytes memory result
    )
        private
        pure
        returns (Status status, AllowanceConsumption[] memory consumptions)
    {
        // The header alone is 3 words.
        if (result.length < 96) {
            return (Status.CustomConditionInvalidResult, consumptions);
        }

        // Decoded as uint256: abi.decode of a bool reverts on a dirty word,
        // which must instead surface as an invalid result status.
        (uint256 success, uint256 offset, uint256 count) = abi.decode(
            result,
            (uint256, uint256, uint256)
        );

        // The pairs must fill the tail exactly. Count is bounded before the
        // multiplication so it cannot overflow.
        if (
            success > 1 ||
            offset != 0x40 ||
            count > (result.length - 96) / 64 ||
            result.length != 96 + count * 64
        ) {
            return (Status.CustomConditionInvalidResult, consumptions);
        }

        if (success == 0) {
            return (Status.CustomConditionViolation, consumptions);
        }

        // The layout is canonical, so this decoding cannot fail.
        (, consumptions) = abi.decode(result, (bool, AllowanceConsumption[]));

        return (Status.Ok, consumptions);
    }

    /**
     * @dev Applies each consumption to the running list, in order. The first
     *      failure returns immediately, discarding the adapter's remaining
     *      consumptions.
     */
    function _applyConsumptions(
        Consumption[] memory consumptions,
        AllowanceConsumption[] memory allowanceConsumptions
    ) private view returns (Status, Consumption[] memory) {
        for (uint256 i; i < allowanceConsumptions.length; ++i) {
            Status status;
            (status, consumptions) = AllowanceConsumer.consume(
                consumptions,
                allowanceConsumptions[i].allowanceKey,
                allowanceConsumptions[i].amount
            );
            if (status != Status.Ok) {
                return (status, consumptions);
            }
        }

        return (Status.Ok, consumptions);
    }
}
