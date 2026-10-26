// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.0;

contract TestAvatar {
    receive() external payable {}

    function exec(
        address payable to,
        uint256 value,
        bytes calldata data,
        uint8 operation
    ) external {
        bool success;
        bytes memory response;
        if (operation == 1) (success, ) = to.delegatecall(data);
        else (success, response) = to.call{value: value}(data);
        if (!success) {
            assembly {
                revert(add(response, 0x20), mload(response))
            }
        }
    }

    function execTransactionFromModule(
        address payable to,
        uint256 value,
        bytes calldata data,
        uint8 operation
    ) external returns (bool success) {
        if (operation == 1) (success, ) = to.delegatecall(data);
        else (success, ) = to.call{value: value}(data);
    }

    function execTransactionFromModuleReturnData(
        address to,
        uint256 value,
        bytes memory data,
        uint8 operation
    ) external returns (bool success, bytes memory returnData) {
        if (operation == 1) (success, ) = to.delegatecall(data);
        else (success, returnData) = to.call{value: value}(data);
    }
}
