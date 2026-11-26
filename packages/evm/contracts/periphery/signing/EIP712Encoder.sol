// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.21 <0.9.0;

import {Encoding} from "../../evaluator/types/EvaluatorTypes.sol";

/**
 * @dev Flat node in a parent-ordered EIP-712 type tree:
 *      - `parent`: parent index in `types`
 *      - `encoding`: `Static`, `Dynamic`, `Tuple` or `Array`
 *      - `typeHash`: EIP-712 `typeHash` for structs, `bytes32(0)` otherwise
 */
struct TypeNodeFlat {
    uint256 parent;
    Encoding encoding;
    bytes32 typeHash;
}

/// @dev Materialized node of a `TypeNodeFlat[]` tree.
struct TypeNode {
    Encoding encoding;
    TypeNode[] children;
    bytes32 typeHash;
}

/**
 * @title EIP712Encoder
 * @notice Hashes EIP-712 structured data directly over ABI-encoded calldata.
 */
library EIP712Encoder {
    error InvalidEIP712Encoding();

    /**
     * @dev Computes the hash of an EIP-712 message:
     *      `keccak256("\x19\x01" || domainSeparator || messageHash)`.
     * @param domain  ABI-encoded `EIP712Domain` tuple body.
     * @param message ABI-encoded primary message tuple body.
     * @param types   Flattened type tree (`types[0]` = domain, `types[1]` = message).
     */
    function hashTypedMessage(
        bytes calldata domain,
        bytes calldata message,
        TypeNodeFlat[] calldata types
    ) internal pure returns (bytes32 result) {
        bytes32 domainSeparator = _hashStruct(domain, types, 0);
        bytes32 messageHash = _hashStruct(message, types, 1);

        assembly {
            let ptr := mload(0x40)
            mstore(ptr, hex"1901")
            mstore(add(ptr, 0x02), domainSeparator)
            mstore(add(ptr, 0x22), messageHash)
            result := keccak256(ptr, 0x42)
        }
    }

    /**
     * @dev Computes the EIP-712 domain separator `hashStruct(EIP712Domain)`.
     * @param data  ABI-encoded `EIP712Domain` tuple body.
     * @param types Flattened type tree (`types[0]` = domain).
     */
    function hashTypedDomain(
        bytes calldata data,
        TypeNodeFlat[] calldata types
    ) internal pure returns (bytes32) {
        return _hashStruct(data, types, 0);
    }

    /**
     * @dev Hashes the root struct at `types[index]` over `data` from offset 0.
     *      Requires `types[index]` to be a struct (`Tuple` with non-zero `typeHash`).
     */
    function _hashStruct(
        bytes calldata data,
        TypeNodeFlat[] calldata types,
        uint256 index
    ) private pure returns (bytes32) {
        if (index >= types.length) {
            revert InvalidEIP712Encoding();
        }

        TypeNode memory root = _toTree(types, index);
        if (root.encoding != Encoding.Tuple || root.typeHash == bytes32(0)) {
            revert InvalidEIP712Encoding();
        }

        return _hashField(data, root, 0);
    }

    /**
     * @dev Encodes and hashes the value of `node` at byte offset `location` in `data`.
     *      `location` points to the 32-byte word (`Static`), length word (`Dynamic`),
     *      count word (`Array`), or head block (`Tuple`).
     */
    function _hashField(
        bytes calldata data,
        TypeNode memory node,
        uint256 location
    ) private pure returns (bytes32) {
        Encoding encoding = node.encoding;

        if (encoding == Encoding.Static) {
            return _word(data, location);
        }

        if (encoding == Encoding.Dynamic) {
            uint256 left = location + 32;
            uint256 right = left + uint256(_word(data, location));

            if (right > data.length) {
                revert InvalidEIP712Encoding();
            }

            return keccak256(data[left:right]);
        }

        if (encoding == Encoding.Array) {
            // arrays hash as the concatenation of element encodings,
            // so a non-zero typeHash would yield a non-standard digest
            if (node.typeHash != bytes32(0)) {
                revert InvalidEIP712Encoding();
            }

            return
                _hashBlock(
                    data,
                    node,
                    location + 32,
                    uint256(_word(data, location))
                );
        }

        if (encoding == Encoding.Tuple) {
            return _hashBlock(data, node, location, node.children.length);
        }

        revert InvalidEIP712Encoding();
    }

    /**
     * @dev Hashes a head/tail ABI block starting at `blockLocation`.
     *      Dynamic child offsets are resolved relative to `blockLocation`.
     *      For `Array`, `node.children[0]` is repeated `childCount` times;
     *      for structs (`node.typeHash != 0`), `typeHash` is prepended.
     */
    function _hashBlock(
        bytes calldata data,
        TypeNode memory node,
        uint256 blockLocation,
        uint256 childCount
    ) private pure returns (bytes32) {
        bool isArray = node.encoding == Encoding.Array;
        if (isArray && node.children.length != 1) {
            revert InvalidEIP712Encoding();
        }

        bytes32[] memory result = new bytes32[](childCount);
        uint256 headOffset;

        for (uint256 i = 0; i < childCount; ++i) {
            TypeNode memory child = node.children[isArray ? 0 : i];
            (uint256 childLocation, uint256 childInlineSize) = _childLocation(
                data,
                blockLocation,
                headOffset,
                child
            );

            result[i] = _hashField(data, child, childLocation);
            headOffset += childInlineSize > 0 ? childInlineSize : 32;
        }

        return
            keccak256(
                node.typeHash != bytes32(0)
                    ? abi.encodePacked(node.typeHash, result)
                    : abi.encodePacked(result)
            );
    }

    /**
     * @dev Resolves a child's byte offset in `data` and its inline width (`0` if
     *      referenced via a 32-byte head offset relative to `blockLocation`).
     */
    function _childLocation(
        bytes calldata data,
        uint256 blockLocation,
        uint256 headOffset,
        TypeNode memory child
    ) private pure returns (uint256 childLocation, uint256 childInlineSize) {
        uint256 headLocation = blockLocation + headOffset;

        childInlineSize = _inlineSize(child);

        if (childInlineSize > 0) {
            return (headLocation, childInlineSize);
        }

        // The offset must point past its own head slot
        uint256 tailOffset = uint256(_word(data, headLocation));
        if (tailOffset < headOffset + 32) {
            revert InvalidEIP712Encoding();
        }

        return (blockLocation + tailOffset, 0);
    }

    /**
     * @dev Returns a child node's inline byte width in its parent head, or `0`
     *      if it is dynamic. Empty nested tuples are rejected so `0` remains
     *      an unambiguous sentinel.
     */
    function _inlineSize(
        TypeNode memory node
    ) private pure returns (uint256 inlineSize) {
        Encoding encoding = node.encoding;

        if (encoding == Encoding.Dynamic || encoding == Encoding.Array) {
            return 0;
        }

        if (encoding == Encoding.Static) {
            return 32;
        }

        if (encoding != Encoding.Tuple || node.children.length == 0) {
            revert InvalidEIP712Encoding();
        }

        for (uint256 i = 0; i < node.children.length; ++i) {
            uint256 childInlineSize = _inlineSize(node.children[i]);
            if (childInlineSize == 0) {
                return 0;
            }
            inlineSize += childInlineSize;
        }
    }

    /**
     * @dev Materializes the subtree rooted at `types[index]`.
     *      Children must appear after their parent (`i > index`)
     */
    function _toTree(
        TypeNodeFlat[] calldata types,
        uint256 index
    ) private pure returns (TypeNode memory node) {
        node.encoding = types[index].encoding;
        node.typeHash = types[index].typeHash;

        // Count children (nodes where parent == index)
        uint256 childCount = 0;
        uint256 len = types.length;
        for (uint256 i = index + 1; i < len; ++i) {
            if (types[i].parent == index) {
                ++childCount;
            }
        }

        if (childCount > 0) {
            node.children = new TypeNode[](childCount);
            uint256 childIndex = 0;
            for (uint256 i = index + 1; childIndex < childCount; ++i) {
                if (types[i].parent == index) {
                    node.children[childIndex++] = _toTree(types, i);
                }
            }
        }
    }

    /// @dev Loads the 32-byte word at `location` in `data`
    function _word(
        bytes calldata data,
        uint256 location
    ) private pure returns (bytes32 result) {
        if (location + 32 > data.length) {
            revert InvalidEIP712Encoding();
        }

        assembly {
            result := calldataload(add(data.offset, location))
        }
    }
}
