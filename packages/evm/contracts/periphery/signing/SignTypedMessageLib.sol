// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.21 <0.9.0;

import "./EIP712Encoder.sol";

import "../interfaces/SafeStorage.sol";

/**
 * @title SignTypedMessageLib - Marks (typed) messages as signed in SafeStorage
 *
 * @dev Execution context:
 *        Signing calls must be executed via `delegatecall`, reverting with
 *        `OnlyDelegateCall` otherwise. Callers are responsible for executing
 *        in a Safe context.
 */
contract SignTypedMessageLib is SafeStorage {
    /// @dev Deployment address of the contract.
    address public immutable deployedAt;

    /// @dev Emitted with the SafeMessage hash stored as the approval key.
    event SignMsg(bytes32 indexed msgHash);

    /// @dev The EIP-712 type hash of Safe's message wrapper.
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
     * @notice Marks raw bytes as signed, matching Safe's SignMessageLib
     *
     * @dev Wraps `message` directly in `SafeMessage`, without first applying a
     *      personal-sign prefix or computing a typed-data digest.
     *
     * @dev Storage write:
     *        `signedMessages[keccak256(safeMessagePreimage(message))] = 1`
     *
     * @dev Verification:
     *        - `isValidSignature(bytes32 digest, "") == 0x1626ba7e`
     *          when `message = abi.encode(digest)`.
     *        - `isValidSignature(bytes message, "") == 0x20c13b0b`
     *          for arbitrary-length `message` (legacy; Safe 1.3.0 and 1.4.1 only).
     *
     * @param message Raw bytes to approve, typically a 32-byte digest
     */
    function signMessage(bytes calldata message) external {
        if (address(this) == deployedAt) revert OnlyDelegateCall();
        bytes32 safeMessageHash = keccak256(safeMessagePreimage(message));

        signedMessages[safeMessageHash] = 1;
        emit SignMsg(safeMessageHash);
    }

    /**
     * @notice Marks an EIP-191 (`personal_sign`) message as signed
     *
     * @dev Computes `digest` using the EIP-191 personal-sign prefix and decimal
     *      byte length, then wraps `abi.encode(digest)` in `SafeMessage`.
     *
     * @dev Storage write:
     *        `signedMessages[keccak256(safeMessagePreimage(abi.encode(digest)))] = 1`
     *
     * @dev Verification:
     *        `isValidSignature(bytes32 digest, "") == 0x1626ba7e`
     *        where `digest` is the EIP-191 personal-sign hash.
     *
     * @param message Raw message bytes before EIP-191 prefixing
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
     * @notice Marks an EIP-712 typed structured message as signed
     *
     * @dev Computes `digest` with `EIP712Encoder`, then wraps `abi.encode(digest)`
     *      in `SafeMessage`. Also reachable under unrecognized selectors via
     *      `fallback`.
     *
     * @dev Storage write:
     *        `signedMessages[keccak256(safeMessagePreimage(abi.encode(digest)))] = 1`
     *
     * @dev Verification:
     *        `isValidSignature(bytes32 digest, "") == 0x1626ba7e`
     *        where `digest` is the EIP-712 typed-data hash.
     *
     * @param domain ABI-encoded fields of the EIP-712 domain struct
     * @param message ABI-encoded fields of the EIP-712 primary message struct
     * @param types Flattened EIP-712 type layout for `domain` and `message`
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
     * @notice Builds the EIP-712 `SafeMessage` approval preimage
     * @dev Reads the domain separator from `ISafe(address(this)).domainSeparator()`.
     * @param message Bytes to wrap in `SafeMessage(bytes message)`
     * @return The preimage whose `keccak256` hash is the SafeMessage approval key
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
     * @notice Builds a SafeMessage approval preimage for EIP-712 typed data
     * @dev Computes the EIP-712 `digest` with `EIP712Encoder` and wraps
     *      `abi.encode(digest)` using `safeMessagePreimage`.
     * @param domain ABI-encoded fields of the EIP-712 domain struct
     * @param message ABI-encoded fields of the EIP-712 primary message struct
     * @param types Flattened EIP-712 type layout for `domain` and `message`
     * @return The preimage whose `keccak256` hash is the SafeMessage approval key
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
     * @notice Dispatches unrecognized selectors to `signTypedMessage`
     * @dev Decodes the same arguments as `signTypedMessage`, allowing Roles
     *      permissions to use selector aliases for different type layouts.
     *      Permissions must also constrain `types` to enforce the intended layout.
     *      Reverts with `InvalidCalldata` if arguments lie outside calldata.
     */
    fallback() external {
        // selector and three head words
        if (msg.data.length < 0x64) revert InvalidCalldata();

        bytes calldata domain;
        bytes calldata message;
        TypeNodeFlat[] calldata types;

        (uint256 offset, uint256 length) = _locateArgument(0x04, 1);
        assembly {
            domain.offset := offset
            domain.length := length
        }

        (offset, length) = _locateArgument(0x24, 1);
        assembly {
            message.offset := offset
            message.length := length
        }

        // each TypeNodeFlat takes three words
        (offset, length) = _locateArgument(0x44, 0x60);
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
    function _locateArgument(
        uint256 head,
        uint256 itemSize
    ) private pure returns (uint256 offset, uint256 length) {
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
