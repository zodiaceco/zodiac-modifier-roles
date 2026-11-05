// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../core/evaluate/ConditionEvaluator.sol";
import "../../core/serialize/Integrity.sol";
import "../../core/serialize/ConditionPacker.sol";
import "../../core/serialize/ConditionUnpacker.sol";
import "../../types/Types.sol";
import {ALLOWANCES_SLOT, AVATAR_SLOT} from "../../core/StorageSlots.sol";

/**
 * @dev For testing off-chain evaluators against the contract: runs a
 *      condition tree on calldata exactly as `Roles` does (Integrity →
 *      pack → unpack → evaluate) and returns everything `ConditionViolation`
 *      carries. Call it with `eth_call`; it writes the avatar and the
 *      allowance balances to its own storage first.
 *
 *      Reverts with Integrity's errors for a tree `allowFunction` rejects.
 */
contract EvaluatorHarness {
    struct Call {
        bytes data;
        uint256 value;
        address to;
        Operation operation;
        address avatar;
    }

    function evaluate(
        Call calldata call,
        ConditionFlat[] memory conditions,
        bytes32[] memory allowanceKeys,
        uint128[] memory allowanceBalances
    )
        external
        returns (uint8 status, uint256 violatedNodeIndex, uint256 location)
    {
        Integrity.enforce(conditions);

        address avatar = call.avatar;
        assembly {
            sstore(AVATAR_SLOT, avatar)
        }
        for (uint256 i; i < allowanceKeys.length; ++i) {
            bytes32 key = allowanceKeys[i];
            // period 0: the balance as given, no refill
            uint256 word2 = (uint256(type(uint64).max) << 192) |
                (uint256(allowanceBalances[i]) << 64);
            assembly {
                mstore(0x00, key)
                mstore(0x20, ALLOWANCES_SLOT)
                let slot := keccak256(0x00, 0x40)
                sstore(slot, 0)
                sstore(add(slot, 1), word2)
            }
        }

        (Condition memory root, uint256 maxPluck) = ConditionUnpacker.unpack(
            ConditionPacker.pack(conditions)
        );
        Result memory result = ConditionEvaluator.evaluate(
            call.data,
            0,
            root,
            new Consumption[](0),
            Context({
                to: call.to,
                value: call.value,
                operation: call.operation,
                pluckedValues: new bytes32[](maxPluck),
                pluckedLocations: new uint256[](maxPluck)
            })
        );
        return (
            uint8(result.status),
            result.violatedNodeIndex,
            result.payloadLocation
        );
    }
}
