// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../periphery/interfaces/ICustomCondition.sol";

contract TestCustomChecker is ICustomCondition {
    function check(
        address,
        uint256,
        bytes calldata data,
        Operation operation,
        uint256 location,
        uint256 size,
        bytes calldata,
        bytes32[] calldata
    )
        public
        pure
        returns (bool success, AllowanceConsumption[] memory consumptions)
    {
        uint256 param = uint256(bytes32(data[location:location + size]));

        if (operation != Operation.Call) {
            return (false, consumptions);
        }

        return (param > 100, consumptions);
    }
}

/// @dev Returns one consumption per raw bytes32 key concatenated in `extra`.
contract TestCustomCheckerConsuming is ICustomCondition {
    function check(
        address,
        uint256,
        bytes calldata data,
        Operation,
        uint256 location,
        uint256 size,
        bytes calldata extra,
        bytes32[] calldata
    )
        external
        pure
        returns (bool success, AllowanceConsumption[] memory consumptions)
    {
        uint256 amount = uint256(bytes32(data[location:location + size]));
        uint256 count = extra.length / 32;
        consumptions = new AllowanceConsumption[](count);

        for (uint256 i; i < count; ++i) {
            bytes32 allowanceKey = bytes32(extra[i * 32:(i + 1) * 32]);
            consumptions[i] = AllowanceConsumption(allowanceKey, amount);
        }

        return (true, consumptions);
    }
}

contract TestCustomCheckerNoInterface {
    function dummy() external pure returns (uint256) {
        return 42;
    }
}

contract TestCustomCheckerReverting is ICustomCondition {
    function check(
        address,
        uint256,
        bytes calldata,
        Operation,
        uint256,
        uint256,
        bytes calldata,
        bytes32[] calldata
    ) public pure returns (bool, AllowanceConsumption[] memory) {
        revert("CustomChecker: intentional revert");
    }
}

contract TestCustomCheckerWrongReturn {
    function check(
        address,
        uint256,
        bytes calldata,
        uint8,
        uint256,
        uint256,
        bytes calldata,
        bytes32[] memory
    ) public pure returns (uint256, uint256) {
        return (999, 0);
    }
}

/// @dev Produces malformed return data selected by the first byte of `extra`.
contract TestCustomCheckerMalformed {
    function check(
        address,
        uint256,
        bytes calldata,
        Operation,
        uint256,
        uint256,
        bytes calldata extra,
        bytes32[] calldata
    ) external pure {
        uint8 mode = uint8(extra[0]);
        assembly {
            switch mode
            case 0 {
                // Non-canonical array offset.
                mstore(0, 1)
                mstore(0x20, 0x60)
                mstore(0x40, 0)
                return(0, 0x60)
            }
            case 2 {
                // Dirty success word (not 0 or 1) in a canonical layout.
                mstore(0, 2)
                mstore(0x20, 0x40)
                mstore(0x40, 0)
                return(0, 0x60)
            }
            default {
                // One consumption missing its amount word.
                mstore(0, 1)
                mstore(0x20, 0x40)
                mstore(0x40, 1)
                mstore(0x60, 0x1234)
                return(0, 0x80)
            }
        }
    }
}
