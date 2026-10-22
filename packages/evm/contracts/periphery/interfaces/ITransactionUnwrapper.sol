// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "@gnosis-guild/zodiac-core/contracts/core/Operation.sol";

struct UnwrappedTransaction {
    Operation operation;
    address to;
    uint256 value;
    // We wanna deal in calldata slices. We return location, let invoker slice
    uint256 dataLocation;
    uint256 dataSize;
}

interface ITransactionUnwrapper {
    function unwrap(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation
    ) external view returns (UnwrappedTransaction[] memory result);
}
