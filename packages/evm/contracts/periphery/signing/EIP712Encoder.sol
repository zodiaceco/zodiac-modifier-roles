// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.21 <0.9.0;

import {Encoding} from "../../types/Condition.sol";

/**
 * @dev EIP-712 has two recursive layers:
 *
 *      1. Type recursion
 *         `typeHash(T)` is derived from the canonical type string of `T`,
 *         which includes every referenced struct reachable from `T`.
 *         That dependency expansion happens off-chain in the SDK, so this
 *         contract receives each struct's precomputed `typeHash`.
 *
 *      2. Value recursion
 *         `hashStruct(value)` walks the concrete value tree bottom-up:
 *         - static fields contribute their ABI word directly
 *         - `string` / `bytes` contribute `keccak256(contents)`
 *         - nested structs contribute `hashStruct(nestedValue)`
 *         - arrays contribute `keccak256(encoded element hashes)`
 *
 *      This encoder implements the second part directly over ABI locations.
 */

struct TypeNodeFlat {
    uint256 parent;
    Encoding encoding;
    bytes32 typeHash;
}

struct TypeNode {
    Encoding encoding;
    TypeNode[] children;
    bytes32 typeHash;
}

/**
 * @title EIP712Encoder - Encodes and hashes EIP-712 typed structured data
 *
 * @author gnosisguild
 */
library EIP712Encoder {
    error InvalidEIP712Encoding();

    /**
     * @dev Computes the hash of an EIP-712 message.
     * @param domain  The encoded domain data.
     * @param message The encoded message data.
     * @param types   Flattened type nodes for domain and message.
     */
    function hashTypedMessage(
        bytes calldata domain,
        bytes calldata message,
        TypeNodeFlat[] calldata types
    ) internal pure returns (bytes32 result) {
        (bytes32 domainSeparator, bytes32 messageHash) = (
            _hashStruct(domain, types, 0),
            _hashStruct(message, types, 1)
        );

        assembly {
            let ptr := mload(0x40)
            mstore(ptr, hex"1901")
            mstore(add(ptr, 0x02), domainSeparator)
            mstore(add(ptr, 0x22), messageHash)
            result := keccak256(ptr, 0x42)
        }
    }

    /**
     * @dev Computes the hash of an EIP-712 domain.
     * @param data  The encoded domain data.
     * @param types Type nodes for the domain.
     */
    function hashTypedDomain(
        bytes calldata data,
        TypeNodeFlat[] calldata types
    ) internal pure returns (bytes32) {
        return _hashStruct(data, types, 0);
    }

    /**
     * @dev Struct hashing entrypoint. `data` is the root tuple block itself,
     *      so hashing starts from ABI location 0 on the root struct node.
     *
     * @param data  Encoded structure data.
     * @param types Type nodes.
     * @param index Type definition entrypoint.
     */
    function _hashStruct(
        bytes calldata data,
        TypeNodeFlat[] calldata types,
        uint256 index
    ) private pure returns (bytes32 result) {
        TypeNode memory root = _toTree(types, index);
        if (root.encoding != Encoding.Tuple || root.typeHash == bytes32(0)) {
            revert InvalidEIP712Encoding();
        }

        return _hashField(data, root, 0);
    }

    /**
     * @dev EIP-712 field encoder:
     *      - static fields are read directly from ABI encoding
     *      - string/bytes fields are keccak256(content)
     *      - structs hash as keccak256(typeHash || encoded fields)
     *      - arrays hash as keccak256(encoded elements)
     *
     * @param data     Encoded input data.
     * @param layout   The type node for the field.
     * @param location Absolute ABI location of the field value.
     */
    function _hashField(
        bytes calldata data,
        TypeNode memory layout,
        uint256 location
    ) private pure returns (bytes32) {
        Encoding encoding = layout.encoding;

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
            return
                _hashBlock(
                    data,
                    layout,
                    location + 32,
                    uint256(_word(data, location)),
                    true
                );
        }

        if (encoding == Encoding.Tuple) {
            return
                _hashBlock(
                    data,
                    layout,
                    location,
                    layout.children.length,
                    false
                );
        }

        revert InvalidEIP712Encoding();
    }

    /**
     * @dev Hashes a tuple-style block.
     *
     *      Structs and fixed-length arrays are both encoded as tuple blocks.
     *      Dynamic arrays also use the same head/tail layout once the leading
     *      length word has been skipped. `isArray` only controls whether a
     *      single child layout is repeated for every element.
     */
    function _hashBlock(
        bytes calldata data,
        TypeNode memory layout,
        uint256 blockLocation,
        uint256 childCount,
        bool isArray
    ) private pure returns (bytes32) {
        if (isArray && layout.children.length != 1) {
            revert InvalidEIP712Encoding();
        }

        bytes32[] memory result = new bytes32[](childCount);
        uint256 headOffset;

        for (uint256 i = 0; i < childCount; ++i) {
            TypeNode memory child = layout.children[isArray ? 0 : i];
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
                layout.typeHash != bytes32(0)
                    ? abi.encodePacked(layout.typeHash, result)
                    : abi.encodePacked(result)
            );
    }

    /**
     * @dev Resolves the absolute location of a child within a tuple/array
     *      block. Static children are inlined in the head; dynamic children
     *      store a relative offset into the tail.
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
            if (headLocation + 32 > data.length) {
                revert InvalidEIP712Encoding();
            }
            return (headLocation, childInlineSize);
        }

        if (headLocation + 32 > data.length) {
            revert InvalidEIP712Encoding();
        }

        uint256 tailOffset = uint256(_word(data, headLocation));
        if (tailOffset <= headOffset) {
            revert InvalidEIP712Encoding();
        }

        childLocation = blockLocation + tailOffset;
        if (childLocation + 32 > data.length) {
            revert InvalidEIP712Encoding();
        }

        return (childLocation, 0);
    }

    /**
     * @dev Computes how a node occupies a parent ABI head slot.
     *      `0` means the value is represented by a 32-byte offset.
     *      Non-zero means the value is inlined and occupies that many bytes.
     *
     *      Empty tuples are rejected so `0` remains an unambiguous sentinel.
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

        if (encoding != Encoding.Tuple) {
            revert InvalidEIP712Encoding();
        }

        if (node.children.length == 0) {
            revert InvalidEIP712Encoding();
        }

        for (uint256 i = 0; i < node.children.length; ++i) {
            TypeNode memory child = node.children[i];
            uint256 childInlineSize = _inlineSize(child);
            if (childInlineSize == 0) {
                return 0;
            }
            inlineSize += childInlineSize;
        }
    }

    /**
     * @dev Builds a TypeNode tree from TypeNodeFlat array.
     */
    function _toTree(
        TypeNodeFlat[] calldata types,
        uint256 index
    ) private pure returns (TypeNode memory layout) {
        layout.encoding = types[index].encoding;
        layout.typeHash = types[index].typeHash;

        // Count children (nodes where parent == index)
        uint256 childCount = 0;
        uint256 len = types.length;
        for (uint256 i = index + 1; i < len; ++i) {
            if (types[i].parent == index) {
                ++childCount;
            }
        }

        if (childCount > 0) {
            layout.children = new TypeNode[](childCount);
            uint256 childIndex = 0;
            for (uint256 i = index + 1; childIndex < childCount; ++i) {
                if (types[i].parent == index) {
                    layout.children[childIndex++] = _toTree(types, i);
                }
            }
        }
    }

    /**
     * @dev Loads a single 32-byte ABI word from calldata.
     */
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
