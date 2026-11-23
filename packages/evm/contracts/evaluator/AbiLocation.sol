// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Condition, Encoding, Span} from "./types/EvaluatorTypes.sol";

/**
 * @title AbiLocation
 * @notice Locates and slices ABI-encoded values in calldata.
 *
 * @dev A position is a `bytes calldata` slice, never a bare offset: every
 *      slice is obtained by narrowing one already held after checking bounds.
 *
 *      Guarantees (for an `Integrity`-valid condition tree):
 *      - Containment: every returned slice lies inside the input slice, so
 *        nothing can read past its container.
 *      - Exact ABI regions: `sliceEncoded` requires tails back-to-back in order
 *        (no gaps, shared tails, or reordering) and zero padding, so the slice
 *        is one clean encoded value and nothing else.
 *      - No reverts on bad calldata: truncated or malformed calldata returns
 *        `ok = false`.
 *
 *      Layout comes from `inlineSize`: `> 0` sits in place, `0` is reached
 *      through a 32-byte offset in the head.
 *
 *      Trust base: `fromSpan`, `offsetOf`, `_bytesAt`, and `_wordAt` are the
 *      only unchecked assembly primitives. Callers verify bounds first, and a
 *      `Span` is only sound if produced by `toSpan` (or zero for an empty
 *      slice).
 *
 * @author gnosisguild
 */
library AbiLocation {
    /*//////////////////////////////////////////////////////////////
                              NAVIGATION
    //////////////////////////////////////////////////////////////*/

    /**
     * @dev Locates the child spans of a container in `data`. `data` starts at
     *      the count word for `Array`, and at the head block for `Tuple` or
     *      `AbiEncoded` (past payload length and `leadingBytes`). Inlined
     *      children get their exact slot; referenced ones get the suffix from
     *      their offset to the end of `data`.
     */
    function children(
        bytes calldata data,
        Condition memory condition
    ) internal pure returns (Span[] memory result, bool ok) {
        Condition[] memory nodes = condition.children;
        if (condition.encoding == Encoding.Array) {
            return elements(data, nodes[0].inlineSize);
        }

        result = new Span[](nodes.length);
        uint256 head;
        for (uint256 i; i < nodes.length; ++i) {
            (result[i], head, ok) = _child(data, head, nodes[i].inlineSize);
            if (!ok) return (result, false);
        }
        return (result, true);
    }

    /**
     * @dev Locates every element of an array in `data`, starting at its
     *      32-byte count word. `elementSize` is the element's `inlineSize`
     *      (`> 0` inlined, `0` referenced as a suffix to the end of `data`).
     */
    function elements(
        bytes calldata data,
        uint256 elementSize
    ) internal pure returns (Span[] memory result, bool ok) {
        bytes calldata body;
        uint256 count;
        (body, count, ok) = _array(data, elementSize);
        if (!ok) return (result, false);

        result = new Span[](count);
        uint256 head;
        for (uint256 i; i < count; ++i) {
            (result[i], head, ok) = _child(body, head, elementSize);
            if (!ok) return (result, false);
        }
        return (result, true);
    }

    /*//////////////////////////////////////////////////////////////
                              EXTRACTION
    //////////////////////////////////////////////////////////////*/

    /**
     * @dev Slices the content bytes of a value, without ABI length prefix or
     *      padding:
     *      - `inlineSize > 0`: `data[0:inlineSize]` (inlined or `Slice` window)
     *      - `inlineSize == 0`: `data[32:32 + length]` (`Dynamic`/`AbiEncoded`)
     */
    function slice(
        bytes calldata data,
        uint256 inlineSize
    ) internal pure returns (bytes calldata result, bool ok) {
        if (inlineSize > 0) {
            if (inlineSize > data.length) return (data, false);
            return (_bytesAt(data, 0, inlineSize), true);
        }
        if (data.length < 32) return (data, false);
        uint256 length = _wordAt(data, 0);
        if (length > data.length - 32) return (data, false);
        return (_bytesAt(data, 32, length), true);
    }

    /**
     * @dev Slices the full ABI encoding of `condition` at `data` as one
     *      contiguous byte range. Rejects gaps, shared or out-of-order tails,
     *      and non-zero padding.
     */
    function sliceEncoded(
        bytes calldata data,
        Condition memory condition
    ) internal pure returns (bytes calldata result, bool ok) {
        // 1. Inlined: fixed size from the condition tree
        if (condition.inlineSize > 0) {
            if (condition.inlineSize > data.length) return (data, false);
            return (_bytesAt(data, 0, condition.inlineSize), true);
        }

        // 2. Dynamic (`bytes`/`string`) or nested `AbiEncoded` (as `bytes`):
        //    | length (32) | payload | padding to 32-byte word |
        Encoding encoding = condition.encoding;
        if (encoding == Encoding.Dynamic || encoding == Encoding.AbiEncoded) {
            bytes calldata payload;
            (payload, ok) = slice(data, 0);
            if (!ok) return (data, false);

            uint256 padded = (payload.length + 31) & ~uint256(31);
            if (padded > data.length - 32) return (data, false);

            // Trailing padding bytes in the last word must be zero
            uint256 rest = payload.length & 31;
            if (rest != 0 && _wordAt(data, padded) << (rest * 8) != 0) {
                return (data, false);
            }
            return (_bytesAt(data, 0, 32 + padded), true);
        }

        // 3. Logical combinator (`And`/`Or`): no encoding of its own; delegate
        //    to the first child that yields a region
        Condition[] memory nodes = condition.children;
        uint256 count = nodes.length;
        if (encoding == Encoding.None) {
            for (uint256 i; i < count; ++i) {
                (result, ok) = sliceEncoded(data, nodes[i]);
                if (ok) return (result, true);
            }
            return (data, false);
        }

        // 4. Array or Tuple: place `cursor` at the end of the head
        //    (static-element arrays have no tails and return early)
        bytes calldata body = data;
        uint256 cursor;
        if (encoding == Encoding.Array) {
            uint256 elementSize = nodes[0].inlineSize;
            (body, count, ok) = _array(data, elementSize);
            if (!ok) return (data, false);

            if (elementSize > 0) {
                return (_bytesAt(data, 0, 32 + count * elementSize), true);
            }
            cursor = count * 32;
        } else if (encoding == Encoding.Tuple) {
            for (uint256 i; i < count; ++i) {
                cursor += _slotSize(nodes[i].inlineSize);
            }
            if (cursor > body.length) return (data, false);
        } else {
            return (data, false);
        }

        // 5. Walk head and tails in lockstep (`offset == cursor`)
        uint256 head;
        for (uint256 i; i < count; ++i) {
            Condition memory child = nodes[encoding == Encoding.Array ? 0 : i];
            if (child.inlineSize > 0) {
                head += child.inlineSize;
                continue;
            }
            if (_wordAt(body, head) != cursor) return (data, false);
            head += 32;

            bytes calldata childRegion;
            (childRegion, ok) = sliceEncoded(_bytesAt(body, cursor), child);
            if (!ok) return (data, false);
            cursor += childRegion.length;
        }

        // Bounded by construction: `cursor <= body.length` holds initially and
        // each recursive `sliceEncoded` fits within `body[cursor:]`.
        uint256 total = (encoding == Encoding.Array ? 32 : 0) + cursor;
        return (_bytesAt(data, 0, total), true);
    }

    /*//////////////////////////////////////////////////////////////
                                 SPANS
    //////////////////////////////////////////////////////////////*/

    /// @dev Packs `data` into a `Span` (`offset` low 128, `length` high 128).
    function toSpan(bytes calldata data) internal pure returns (Span result) {
        assembly {
            result := or(data.offset, shl(128, data.length))
        }
    }

    /// @dev Unpacks a `Span` into a calldata slice (unchecked).
    function fromSpan(Span span) internal pure returns (bytes calldata result) {
        assembly {
            result.offset := and(span, sub(shl(128, 1), 1))
            result.length := shr(128, span)
        }
    }

    /// @dev Returns the byte offset of `data` relative to `base`
    ///      (unchecked; `data` must lie in `base`).
    function offsetOf(
        Span base,
        bytes calldata data
    ) internal pure returns (uint256 result) {
        assembly {
            result := sub(data.offset, and(base, sub(shl(128, 1), 1)))
        }
    }

    /*//////////////////////////////////////////////////////////////
                                HELPERS
    //////////////////////////////////////////////////////////////*/

    /// @dev Locates the child at `head` in `body` and returns the next slot.
    function _child(
        bytes calldata body,
        uint256 head,
        uint256 inlineSize
    ) private pure returns (Span span, uint256 next, bool ok) {
        uint256 room = body.length;
        uint256 slotSize = _slotSize(inlineSize);
        if (head > room || slotSize > room - head) {
            return (Span.wrap(0), 0, false);
        }
        next = head + slotSize;

        if (inlineSize > 0) {
            return (toSpan(_bytesAt(body, head, slotSize)), next, true);
        }

        // The offset must point forward past its own slot to at least one
        // word (a length, count, or first slot). It may point short of the end
        // of the head: a `Matches` need not list every field, so the full head
        // size is not known here.
        uint256 offset = _wordAt(body, head);
        if (offset < next || offset > room || room - offset < 32) {
            return (Span.wrap(0), 0, false);
        }
        return (toSpan(_bytesAt(body, offset)), next, true);
    }

    /// @dev Unpacks an array's element block (past its count word) and count.
    ///      Returns `ok = false` if the head (`count` slots) does not fit in
    ///      `data`, bounding `count` (and caller allocation) by the slice size.
    function _array(
        bytes calldata data,
        uint256 elementSize
    ) private pure returns (bytes calldata body, uint256 count, bool ok) {
        if (data.length < 32) return (data, 0, false);
        body = _bytesAt(data, 32);
        count = _wordAt(data, 0);
        ok = count <= body.length / _slotSize(elementSize);
    }

    /// @dev Returns a child's slot size (`inlineSize` if inlined, else 32).
    function _slotSize(uint256 inlineSize) private pure returns (uint256) {
        return inlineSize > 0 ? inlineSize : 32;
    }

    /*//////////////////////////////////////////////////////////////
                          UNCHECKED PRIMITIVES
    //////////////////////////////////////////////////////////////*/

    /// @dev Loads the 32-byte word at `start` in `data`
    ///      (unchecked; caller verifies bounds).
    function _wordAt(
        bytes calldata data,
        uint256 start
    ) private pure returns (uint256 result) {
        assembly {
            result := calldataload(add(data.offset, start))
        }
    }

    /// @dev Returns `data` from `start` to its end
    ///      (unchecked; caller verifies bounds).
    function _bytesAt(
        bytes calldata data,
        uint256 start
    ) private pure returns (bytes calldata result) {
        assembly {
            result.offset := add(data.offset, start)
            result.length := sub(data.length, start)
        }
    }

    /// @dev Returns `length` bytes at `start` in `data`
    ///      (unchecked; caller verifies bounds).
    function _bytesAt(
        bytes calldata data,
        uint256 start,
        uint256 length
    ) private pure returns (bytes calldata result) {
        assembly {
            result.offset := add(data.offset, start)
            result.length := length
        }
    }
}
