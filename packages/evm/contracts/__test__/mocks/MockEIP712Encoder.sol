// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.21 <0.9.0;

import "../../periphery/signing/EIP712Encoder.sol";

/**
 * @title MockEIP712Encoder - Test wrapper for EIP712Encoder
 * @dev Exposes internal EIP712Encoder functions for integration testing
 */
contract MockEIP712Encoder {
    function hashTypedMessage(
        bytes calldata domain,
        bytes calldata message,
        TypeNodeFlat[] calldata types
    ) external pure returns (bytes32) {
        return EIP712Encoder.hashTypedMessage(domain, message, types);
    }

    function hashTypedDomain(
        bytes calldata data,
        TypeNodeFlat[] calldata types
    ) external pure returns (bytes32) {
        return EIP712Encoder.hashTypedDomain(data, types);
    }
}
