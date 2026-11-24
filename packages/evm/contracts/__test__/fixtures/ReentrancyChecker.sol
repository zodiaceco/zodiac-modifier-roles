// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.0;

/// @dev A module and target that, while an execution runs, calls back into
///      Roles with calldata set beforehand, and records how that call ended.
///      `callTwice` makes two calls to Roles in one transaction, so that the
///      second shows whether the first released the (transient) guard.
contract ReentrancyChecker {
    address public immutable roles;
    bytes public reentry;

    bool public attackCalled;
    bool public reentered;
    bytes public reentryResult;
    bool public doNothingCalled;
    bool public probeCalled;
    bytes public firstResult;
    bool public secondSucceeded;

    constructor(address _roles) {
        roles = _roles;
    }

    function setReentry(bytes calldata data) external {
        reentry = data;
    }

    /// @dev Calls Roles with `first`, bubbling a revert and recording what it
    ///      returned, then with `second` if any, recording whether it succeeded.
    function callTwice(bytes calldata first, bytes calldata second) external {
        (bool success, bytes memory result) = roles.call(first);
        if (!success) {
            assembly {
                revert(add(result, 0x20), mload(result))
            }
        }
        firstResult = result;
        if (second.length > 0) (secondSucceeded, ) = roles.call(second);
    }

    /// @dev Called by the avatar during execution. Tries to reenter roles.
    function attack() external {
        attackCalled = true;
        (bool success, bytes memory result) = roles.call(reentry);
        reentered = success;
        reentryResult = result;
    }

    function doNothing() external {
        doNothingCalled = true;
    }

    function probe() external {
        probeCalled = true;
    }

    function fail() external pure {
        revert();
    }
}
