// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.0;

contract TestContract {
    error AnError();

    event Invoked(bytes4 selector);

    fallback() external payable {
        emit Invoked(bytes4(msg.data));
    }

    receive() external payable {
        emit Invoked(bytes4(0));
    }

    function fnThatReverts() public pure {
        revert AnError();
    }

    function fnThatMaybeReverts(
        uint256 a,
        bool maybe
    ) public pure returns (uint256) {
        if (maybe) {
            revert AnError();
        }
        return a;
    }
}
