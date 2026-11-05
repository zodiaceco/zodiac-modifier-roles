// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../periphery/interfaces/ICustomCondition.sol";

/**
 * @dev A custom condition for tests: passes when the last byte of the value
 *      it checks is even. Off-chain tests simulate it with the same rule.
 */
contract EvenLastByteCondition is ICustomCondition {
    function check(
        address,
        uint256,
        bytes calldata data,
        Operation,
        uint256 location,
        uint256 size,
        bytes calldata,
        bytes32[] calldata
    )
        external
        pure
        returns (bool success, AllowanceConsumption[] memory consumptions)
    {
        success = uint8(data[location + size - 1]) % 2 == 0;
        return (success, consumptions);
    }
}
