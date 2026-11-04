// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

/**
 * Logs every call it receives. Under delegatecall, `self` is still this
 * contract's address (an immutable), while `context` is the caller's.
 */
contract MockRecorder {
    address private immutable self = address(this);

    event Called(address self, address context, uint256 value, bytes data);

    fallback() external payable {
        emit Called(self, address(this), msg.value, msg.data);
    }
}

/**
 * Delegatecalls MultiSend with raw calldata, as a Safe does in
 * `execTransactionFromModule(multiSend, 0, data, DelegateCall)`.
 */
contract MockDelegator {
    receive() external payable {}

    function run(address multiSend, bytes calldata data) external {
        (bool ok, ) = multiSend.delegatecall(data);
        require(ok, "multiSend reverted");
    }
}
