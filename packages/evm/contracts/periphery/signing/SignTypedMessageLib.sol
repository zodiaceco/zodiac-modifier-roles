// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.21 <0.9.0;

import "./EIP712Encoder.sol";

import "../interfaces/SafeStorage.sol";

/**
 * @title SignTypedMessageLib - Marks (typed) messages as signed in SafeStorage
 * @author gnosisguild
 */
contract SignTypedMessageLib is SafeStorage {
    /// @dev Deployment address of the contract.
    address public immutable deployedAt;

    /// @dev Event emitted when a Safe signs a message and stores it.
    event SignMsg(bytes32 indexed msgHash);

    /// @dev The EIP-712 type hash used to prefix the message.
    bytes32 private constant safeMessageTypeHash =
        keccak256("SafeMessage(bytes message)");

    /// @dev The library was called directly, not through delegatecall.
    error OnlyDelegateCall();

    /// @dev An argument of a fallback call does not lie within calldata.
    error InvalidCalldata();

    constructor() {
        deployedAt = address(this);
    }

    /**
     * @notice Marks a message as signed
     * @dev The message hash is marked as approved in SafeStorage
     * @dev Can be verified using EIP-1271 validation by passing the
     *      message and empty bytes as the signature
     * @param message The message to be signed
     */
    function signMessage(bytes calldata message) external {
        if (address(this) == deployedAt) revert OnlyDelegateCall();
        bytes32 safeMessageHash = keccak256(safeMessagePreimage(message));

        signedMessages[safeMessageHash] = 1;
        emit SignMsg(safeMessageHash);
    }

    /**
     * @notice Marks a personal_sign message as signed
     * @dev Wraps the message with the EIP-191 prefix before hashing
     * @dev Can be verified using EIP-1271 validation by passing the EIP-191
     *      hash and empty bytes as the signature
     * @param message The raw message text to be signed
     */
    function personalSign(bytes calldata message) external {
        if (address(this) == deployedAt) revert OnlyDelegateCall();
        bytes memory wrapped = abi.encodePacked(
            "\x19Ethereum Signed Message:\n",
            uintToString(message.length),
            message
        );
        bytes32 safeMessageHash = keccak256(
            safeMessagePreimage(abi.encode(keccak256(wrapped)))
        );

        signedMessages[safeMessageHash] = 1;
        emit SignMsg(safeMessageHash);
    }

    /**
     * @notice Mark a typed structured message (EIP-712) as signed
     * @dev The typed message hash is marked as approved in SafeStorage
     * @dev Can be verified using EIP-1271 validation by passing the typed
     *      message hash as the message and empty bytes as the signature. Empty
     *      bytes as signature represent an on-chain signature
     * @param domain  The encoded EIP712 domain
     * @param message The encoded EIP712 message
     * @param types   The flattened EIP712 type nodes
     */
    function signTypedMessage(
        bytes calldata domain,
        bytes calldata message,
        TypeNodeFlat[] calldata types
    ) public {
        if (address(this) == deployedAt) revert OnlyDelegateCall();
        bytes32 safeMessageHash = keccak256(
            safeTypedMessagePreimage(domain, message, types)
        );

        signedMessages[safeMessageHash] = 1;
        emit SignMsg(safeMessageHash);
    }

    /**
     * @notice Builds the EIP-712 preimage for a SafeMessage
     * @dev Follows Safe's internal type schema for signing messages
     *
     * @param message  The message to build the preimage for
     * @return bytes   The EIP-712 preimage (hash it to get the SafeMessage hash)
     */
    function safeMessagePreimage(
        bytes memory message
    ) public view returns (bytes memory) {
        return
            abi.encodePacked(
                bytes2(0x1901),
                ISafe(address(this)).domainSeparator(),
                keccak256(abi.encode(safeMessageTypeHash, keccak256(message)))
            );
    }

    /**
     * @notice Builds the EIP-712 preimage for a typed SafeMessage
     * @dev Follows Safe's internal type schema for signing messages
     *
     * @param domain   The encoded EIP712 domain
     * @param message  The encoded EIP712 message
     * @param types    The flattened EIP712 type nodes
     * @return bytes   The EIP-712 preimage (hash it to get the SafeMessage hash)
     */
    function safeTypedMessagePreimage(
        bytes calldata domain,
        bytes calldata message,
        TypeNodeFlat[] calldata types
    ) public view returns (bytes memory) {
        return
            safeMessagePreimage(
                abi.encode(
                    EIP712Encoder.hashTypedMessage(domain, message, types)
                )
            );
    }

    /**
     * We make the signTypedMessage function available under any selector. This
     * allows scoping different layouts under different signTypedMessage
     * aliases. Useful for expressing roles permissions
     */
    fallback() external {
        bytes calldata domain;
        bytes calldata message;
        TypeNodeFlat[] calldata types;

        (uint256 offset, uint256 length) = _argument(0x04, 1);
        assembly {
            domain.offset := offset
            domain.length := length
        }

        (offset, length) = _argument(0x24, 1);
        assembly {
            message.offset := offset
            message.length := length
        }

        // each TypeNodeFlat takes three words
        (offset, length) = _argument(0x44, 0x60);
        assembly {
            types.offset := offset
            types.length := length
        }

        signTypedMessage(domain, message, types);
    }

    /**
     * @dev Locates a dynamic argument from its head word, and requires its
     *      length word and content to lie within calldata.
     */
    function _argument(
        uint256 head,
        uint256 itemSize
    ) private pure returns (uint256 offset, uint256 length) {
        // selector and three head words
        if (msg.data.length < 0x64) revert InvalidCalldata();

        uint256 pointer;
        assembly {
            pointer := calldataload(head)
        }

        // selector, pointer, length word
        if (pointer > msg.data.length - 0x24) revert InvalidCalldata();
        offset = pointer + 0x24;

        assembly {
            length := calldataload(add(pointer, 0x04))
        }

        if (length > (msg.data.length - offset) / itemSize) {
            revert InvalidCalldata();
        }
    }
}

interface ISafe {
    function domainSeparator() external view returns (bytes32);
}

function uintToString(uint256 value) pure returns (string memory) {
    if (value == 0) {
        return "0";
    }

    uint256 temp = value;
    uint256 digits;
    while (temp != 0) {
        digits++;
        temp /= 10;
    }

    bytes memory buffer = new bytes(digits);
    uint8 asciiZero = 48;
    while (value != 0) {
        digits--;
        uint8 digit = uint8(value % 10);
        buffer[digits] = bytes1(asciiZero + digit);
        value /= 10;
    }

    return string(buffer);
}
