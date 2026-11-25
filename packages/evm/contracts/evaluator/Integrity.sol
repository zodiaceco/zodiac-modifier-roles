// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {ConditionFlat} from "../IEvaluator.sol";
import "./types/EvaluatorError.sol";
import "./types/EvaluatorTypes.sol";

/**
 * @title Integrity
 * @notice Validates a flat condition tree before it is packed and stored.
 *
 * @dev An accepted tree survives packing unchanged, never reads an unwritten
 *      Pluck slot, and is read by the evaluator at the ABI location of every
 *      parameter.
 *
 *      Five passes. The first three are single scans. The types pass
 *      recurses only to compare nested types, and the slots pass walks the
 *      tree in evaluation order:
 *      1. layout:    BFS order, child bounds, inlined sizes, field widths
 *      2. plucks:    one well-formed Pluck per slot
 *      3. operators: encoding, compValue and child count of every node
 *      4. types:     every node describes the value it is evaluated at
 *      5. slots:     every Pluck slot is written before it is read
 */
library Integrity {
    uint256 private constant MAX_CONDITION_COUNT = type(uint16).max;
    uint256 private constant MAX_CHILD_COUNT = (1 << 10) - 1;
    uint256 private constant MAX_INLINED_SIZE = (1 << 13) - 1;
    uint256 private constant MAX_COMP_VALUE_LENGTH = type(uint16).max;
    uint256 private constant MAX_DECIMALS = 27;

    /*
     * What a node is to its parent, as computed by the types pass.
     *
     * A node either reads no calldata where it sits (NON_STRUCTURAL: the
     * ether value, an allowance, a Zip), or describes a value of some ABI
     * type. A type is a word, bytes, or the type of a Tuple, Array or
     * AbiEncoded node, written as TYPE_OF + that node's index:
     * - Tuple:      the types of its children; open if the node is a
     *               Matches, which may list only the first fields
     * - Array:      its element type (`Node.element`)
     * - AbiEncoded: nested calldata, interchangeable with bytes
     */
    uint256 private constant NON_STRUCTURAL = 1;
    uint256 private constant STATIC = 3;
    uint256 private constant DYNAMIC = 4;
    uint256 private constant TYPE_OF = 5;

    struct Node {
        Encoding encoding;
        Operator operator;
        /* layout pass */
        uint256 childStart;
        uint256 childCount;
        bool inlined;
        uint256 inlinedSize;
        /* types pass */
        uint256 kind;
        /// Arrays: the element type
        uint256 element;
        /// The node's type has a fixed size
        bool staticType;
        /// The subtree is a plain type description: Pass nodes only
        bool exact;
        /// The node may be the root: calldata, or And / Or over such nodes
        bool rootOk;
    }

    /// @notice Reverts unless `conditions` is a well-formed condition tree.
    function enforce(ConditionFlat[] memory conditions) external pure {
        Node[] memory nodes = _layout(conditions);
        uint256[] memory plucks = _plucks(conditions, nodes);

        for (uint256 i; i < nodes.length; ++i) {
            _operator(conditions[i].compValue, nodes, plucks, i);
        }

        // Children have higher indices than their parent: bottom-up
        for (uint256 i = nodes.length; i > 0; --i) {
            _type(nodes, i - 1);
        }
        _zipTypes(conditions, nodes, plucks);

        _slots(conditions, nodes, 0, 0);
    }

    /*//////////////////////////////////////////////////////////////
                             1. LAYOUT
    //////////////////////////////////////////////////////////////*/

    /**
     * @dev Checks that the array is a tree in BFS order whose nodes fit the
     *      fields of the packed format, and indexes it: children of a node
     *      are contiguous, so a start and a count locate them.
     */
    function _layout(
        ConditionFlat[] memory conditions
    ) private pure returns (Node[] memory nodes) {
        uint256 count = conditions.length;
        if (count > MAX_CONDITION_COUNT) {
            revert IEvaluatorError.ConditionNodeCountExceedsMax();
        }
        if (count == 0 || conditions[0].parent != 0) {
            revert IEvaluatorError.UnsuitableRootNode();
        }

        nodes = new Node[](count);
        nodes[0].encoding = _decodeEncoding(conditions[0].paramType, 0);
        nodes[0].operator = _decodeOperator(conditions[0].operator, 0);

        for (uint256 i = 1; i < count; ++i) {
            uint256 parent = conditions[i].parent;
            if (parent == i) {
                revert IEvaluatorError.UnsuitableRootNode();
            }
            // Parents come first, and children are grouped by parent
            if (parent < conditions[i - 1].parent || parent > i) {
                revert IEvaluatorError.NotBFS();
            }

            nodes[i].encoding = _decodeEncoding(conditions[i].paramType, i);
            nodes[i].operator = _decodeOperator(conditions[i].operator, i);

            Node memory parentNode = nodes[parent];
            if (parentNode.childCount == 0) parentNode.childStart = i;
            ++parentNode.childCount;
        }

        for (uint256 i; i < count; ++i) {
            if (conditions[i].compValue.length > MAX_COMP_VALUE_LENGTH) {
                revert IEvaluatorError.UnsuitableCompValue(i);
            }
            if (nodes[i].childCount > MAX_CHILD_COUNT) {
                revert IEvaluatorError.ConditionChildCountExceedsMax(i);
            }
        }

        /*
         * Inlined nodes, bottom-up: a node is inlined (encoded in place,
         * with a fixed size) unless it or a descendant is Dynamic, Array or
         * AbiEncoded. A Zip is not inlined and is ignored by its parent.
         * Children have higher indices than their parent.
         */
        for (uint256 next = count; next > 0; --next) {
            uint256 i = next - 1;
            Node memory node = nodes[i];
            if (_isZip(node.operator)) continue;

            Encoding encoding = node.encoding;
            if (
                encoding == Encoding.Dynamic ||
                encoding == Encoding.Array ||
                encoding == Encoding.AbiEncoded
            ) {
                continue;
            }

            bool inlined = true;
            uint256 size;
            for (uint256 j; j < node.childCount; ++j) {
                Node memory child = nodes[node.childStart + j];
                // A Zip is ignored by its parent
                if (_isZip(child.operator)) continue;
                if (!child.inlined) {
                    inlined = false;
                    break;
                }
                if (encoding != Encoding.None) {
                    size += child.inlinedSize;
                } else if (size == 0) {
                    // And / Or are transparent: the size of the value they
                    // sit at, given by the first child that has one
                    size = child.inlinedSize;
                }
            }
            if (!inlined) continue;

            if (encoding == Encoding.Static) size = 32;
            if (size > MAX_INLINED_SIZE) {
                revert IEvaluatorError.ConditionInlinedSizeExceedsMax(i);
            }
            node.inlined = true;
            node.inlinedSize = size;
        }
    }

    /*//////////////////////////////////////////////////////////////
                             2. PLUCKS
    //////////////////////////////////////////////////////////////*/

    /**
     * @dev Checks every Pluck node, and maps each slot to the index + 1 of
     *      the one Pluck that writes it (0: no Pluck writes the slot).
     *
     *      Runs before the operators pass, so that operators that read a
     *      slot (Zip, WithinRatio) can look its Pluck up wherever it sits.
     */
    function _plucks(
        ConditionFlat[] memory conditions,
        Node[] memory nodes
    ) private pure returns (uint256[] memory plucks) {
        plucks = new uint256[](256);

        for (uint256 i; i < nodes.length; ++i) {
            if (nodes[i].operator != Operator.Pluck) continue;

            Encoding encoding = nodes[i].encoding;
            if (
                encoding != Encoding.Static &&
                encoding != Encoding.EtherValue &&
                encoding != Encoding.Array
            ) {
                revert IEvaluatorError.UnsuitableParameterType(i);
            }

            /*
             * One byte: the slot. The packed header stores the slot count,
             * max(slot) + 1, in 8 bits, which caps the slot at 254.
             */
            bytes memory compValue = conditions[i].compValue;
            if (compValue.length != 1 || uint8(compValue[0]) == 255) {
                revert IEvaluatorError.UnsuitableCompValue(i);
            }

            uint8 slot = uint8(compValue[0]);
            if (plucks[slot] != 0) {
                revert IEvaluatorError.DuplicatePluckIndex(i, slot);
            }
            plucks[slot] = i + 1;
        }
    }

    /*//////////////////////////////////////////////////////////////
                            3. OPERATORS
    //////////////////////////////////////////////////////////////*/

    /**
     * @dev The rules of one node that depend on its operator: which
     *      encodings it takes, the shape of its compValue, and how many
     *      children it has.
     */
    function _operator(
        bytes memory compValue,
        Node[] memory nodes,
        uint256[] memory plucks,
        uint256 index
    ) private pure {
        Node memory node = nodes[index];
        Operator op = node.operator;
        Encoding encoding = node.encoding;

        if (op == Operator.Pass) {
            // Any encoding
            _requireNoCompValue(compValue, index);
        } else if (op == Operator.And || op == Operator.Or) {
            _requireEncoding(encoding == Encoding.None, index);
            _requireNoCompValue(compValue, index);
            if (node.childCount == 0) {
                revert IEvaluatorError.UnsuitableChildCount(index);
            }
        } else if (op == Operator.Empty) {
            _requireEncoding(encoding == Encoding.None, index);
            _requireNoCompValue(compValue, index);
            _requireNoChildren(node, index);
        } else if (op == Operator.Matches) {
            _checkMatches(compValue, encoding, index);
        } else if (op == Operator.ArraySome || op == Operator.ArrayEvery) {
            _requireEncoding(encoding == Encoding.Array, index);
            _requireNoCompValue(compValue, index);
            if (node.childCount != 1) {
                revert IEvaluatorError.UnsuitableChildCount(index);
            }
        } else if (op == Operator.ArrayTailMatches) {
            _requireEncoding(encoding == Encoding.Array, index);
            _requireNoCompValue(compValue, index);
        } else if (op == Operator.ZipSome || op == Operator.ZipEvery) {
            _checkZip(compValue, nodes, plucks, index);
        } else if (op == Operator.Slice) {
            _checkSlice(compValue, nodes, index);
        } else if (op == Operator.Pluck) {
            // Checked by the plucks pass
        } else if (op == Operator.EqualToAvatar) {
            _requireEncoding(encoding == Encoding.Static, index);
            _requireNoCompValue(compValue, index);
        } else if (op == Operator.EqualTo) {
            _checkEqualTo(compValue, node, index);
        } else if (
            op == Operator.GreaterThan ||
            op == Operator.LessThan ||
            op == Operator.SignedIntGreaterThan ||
            op == Operator.SignedIntLessThan
        ) {
            _requireEncoding(_isWord(encoding), index);
            _requireCompValue(compValue.length == 32, index);
        } else if (op == Operator.Bitmask) {
            _requireEncoding(
                encoding == Encoding.Static || encoding == Encoding.Dynamic,
                index
            );
            // 2 bytes of shift, then a mask and a value of equal length
            _requireCompValue(
                compValue.length >= 4 && compValue.length % 2 == 0,
                index
            );
        } else if (op == Operator.Custom) {
            _requireEncoding(
                encoding == Encoding.Static ||
                    encoding == Encoding.Dynamic ||
                    encoding == Encoding.Tuple ||
                    encoding == Encoding.Array ||
                    encoding == Encoding.EtherValue,
                index
            );
            // The adapter address, then any extra bytes
            _requireCompValue(compValue.length >= 20, index);
        } else if (op == Operator.WithinRatio) {
            _checkWithinRatio(compValue, nodes, plucks, index);
        } else if (op == Operator.WithinAllowance) {
            _checkWithinAllowance(compValue, encoding, index);
        } else if (op == Operator.CallWithinAllowance) {
            _requireEncoding(encoding == Encoding.None, index);
            _requireCompValue(compValue.length == 32, index);
            _requireNoChildren(node, index);
        } else {
            revert IEvaluatorError.UnsupportedOperator(index);
        }

        /*
         * Leaves: a word, bytes or the ether value has no children (a Slice
         * has one, the check of the bytes it extracts), and neither has a
         * Pass on None or AbiEncoded.
         */
        bool isLeaf = encoding == Encoding.None ||
            encoding == Encoding.AbiEncoded
            ? op == Operator.Pass
            : (encoding == Encoding.Static ||
                encoding == Encoding.Dynamic ||
                encoding == Encoding.EtherValue) && op != Operator.Slice;
        if (isLeaf) {
            _requireNoChildren(node, index);
        }
    }

    function _checkMatches(
        bytes memory compValue,
        Encoding encoding,
        uint256 index
    ) private pure {
        _requireEncoding(
            encoding == Encoding.Tuple ||
                encoding == Encoding.Array ||
                encoding == Encoding.AbiEncoded,
            index
        );

        if (encoding != Encoding.AbiEncoded) {
            _requireNoCompValue(compValue, index);
            return;
        }

        /*
         * AbiEncoded: empty (4 leading bytes, the selector, not compared),
         * or 2 bytes holding the leading byte count, optionally followed by
         * that many bytes (at most 32) to compare the leading bytes with.
         */
        uint256 length = compValue.length;
        if (length == 0 || length == 2) return;
        if (length < 2) revert IEvaluatorError.UnsuitableCompValue(index);

        uint256 leadingBytes = (uint256(uint8(compValue[0])) << 8) |
            uint8(compValue[1]);
        _requireCompValue(
            length == 2 + leadingBytes && leadingBytes <= 32,
            index
        );
    }

    function _checkZip(
        bytes memory compValue,
        Node[] memory nodes,
        uint256[] memory plucks,
        uint256 index
    ) private pure {
        Node memory node = nodes[index];
        _requireEncoding(node.encoding == Encoding.None, index);

        // One slot per zipped array, at least one
        _requireCompValue(compValue.length >= 1, index);

        // One child: a Tuple with one field per zipped array
        if (node.childCount != 1) {
            revert IEvaluatorError.UnsuitableChildCount(index);
        }
        Node memory fields = nodes[node.childStart];
        if (fields.encoding != Encoding.Tuple) {
            revert IEvaluatorError.UnsuitableChildTypeTree(index);
        }
        _requireCompValue(fields.childCount == compValue.length, index);

        // Only the fields are evaluated: an operator on the Tuple itself
        // would never run
        if (fields.operator != Operator.Matches) {
            revert IEvaluatorError.UnsupportedOperator(node.childStart);
        }

        // Each slot written by an Array Pluck. A slot may repeat: its array
        // is then zipped with itself
        for (uint256 i; i < compValue.length; ++i) {
            uint256 pluck = plucks[uint8(compValue[i])];
            _requireCompValue(
                pluck != 0 && nodes[pluck - 1].encoding == Encoding.Array,
                index
            );
        }
    }

    function _checkSlice(
        bytes memory compValue,
        Node[] memory nodes,
        uint256 index
    ) private pure {
        Node memory node = nodes[index];
        _requireEncoding(
            node.encoding == Encoding.Static ||
                node.encoding == Encoding.Dynamic,
            index
        );

        // 2 bytes of shift, 1 byte of size (1 to 32)
        _requireCompValue(compValue.length == 3, index);
        uint8 size = uint8(compValue[2]);
        _requireCompValue(size >= 1 && size <= 32, index);

        // One child, checking the extracted bytes as a word. It must be a
        // leaf: a Slice of a Slice would index into the word, not the value
        if (node.childCount != 1) {
            revert IEvaluatorError.UnsuitableChildCount(index);
        }
        Node memory child = nodes[node.childStart];
        if (
            child.encoding != Encoding.Static ||
            child.childCount != 0 ||
            _navigates(child.operator)
        ) {
            revert IEvaluatorError.SliceChildNotStatic(index);
        }
    }

    function _checkEqualTo(
        bytes memory compValue,
        Node memory node,
        uint256 index
    ) private pure {
        Encoding encoding = node.encoding;
        _requireEncoding(
            encoding != Encoding.None && encoding != Encoding.AbiEncoded,
            index
        );

        uint256 length = compValue.length;
        if (_isWord(encoding)) {
            _requireCompValue(length == 32, index);
        } else if (node.inlined) {
            /*
             * A static Tuple is read over exactly its encoded size, while
             * a compValue longer than a word is hashed before comparing.
             * Unless the lengths match, the two sides are compared in
             * different forms.
             */
            _requireCompValue(length == node.inlinedSize, index);
        } else {
            // Dynamic, or a dynamic Tuple or Array: ABI encoded, at least
            // an offset and one word
            _requireCompValue(length >= 64, index);
        }
    }

    function _checkWithinRatio(
        bytes memory compValue,
        Node[] memory nodes,
        uint256[] memory plucks,
        uint256 index
    ) private pure {
        Node memory node = nodes[index];
        _requireEncoding(node.encoding == Encoding.None, index);

        /*
         * 12 bytes: reference slot, reference decimals, relative slot,
         * relative decimals, minRatio (4), maxRatio (4). Then up to two
         * price adapter blobs.
         */
        uint256 length = compValue.length;
        _requireCompValue(length >= 12, index);
        uint256 offset = 12;
        if (length > offset) {
            offset = _adapterBlob(compValue, offset, index);
        }
        if (length > offset) {
            offset = _adapterBlob(compValue, offset, index);
        }
        _requireCompValue(length == offset, index);

        if (
            uint8(compValue[1]) > MAX_DECIMALS ||
            uint8(compValue[3]) > MAX_DECIMALS
        ) {
            revert IEvaluatorError.AllowanceDecimalsExceedMax(index);
        }

        // Both slots hold a word. A slot no Pluck writes is rejected by the
        // slots pass
        for (uint256 i; i <= 2; i += 2) {
            uint256 pluck = plucks[uint8(compValue[i])];
            if (pluck != 0 && !_isWord(nodes[pluck - 1].encoding)) {
                revert IEvaluatorError.WithinRatioTargetNotStatic(index);
            }
        }

        uint256 minRatio = _uint32(compValue, 4);
        uint256 maxRatio = _uint32(compValue, 8);
        if (minRatio == 0 && maxRatio == 0) {
            revert IEvaluatorError.WithinRatioNoRatioProvided(index);
        }
        if (minRatio != 0 && maxRatio != 0 && minRatio > maxRatio) {
            revert IEvaluatorError.WithinRatioMinExceedsMax(index);
        }

        _requireNoChildren(node, index);
    }

    /// @dev One adapter blob: a length byte, then nothing (no adapter) or
    ///      an adapter address and its params. Returns the offset after it.
    function _adapterBlob(
        bytes memory compValue,
        uint256 offset,
        uint256 index
    ) private pure returns (uint256) {
        uint256 blobLength = uint8(compValue[offset]);
        _requireCompValue(blobLength == 0 || blobLength >= 20, index);
        offset += 1 + blobLength;
        _requireCompValue(offset <= compValue.length, index);
        return offset;
    }

    function _checkWithinAllowance(
        bytes memory compValue,
        Encoding encoding,
        uint256 index
    ) private pure {
        _requireEncoding(_isWord(encoding), index);

        // The allowance key (32), optionally two decimals bytes (2),
        // optionally a price adapter (20) and its params
        uint256 length = compValue.length;
        _requireCompValue(length == 32 || length == 34 || length >= 54, index);
        if (
            length > 32 &&
            (uint8(compValue[32]) > MAX_DECIMALS ||
                uint8(compValue[33]) > MAX_DECIMALS)
        ) {
            revert IEvaluatorError.AllowanceDecimalsExceedMax(index);
        }
    }

    /*//////////////////////////////////////////////////////////////
                              4. TYPES
    //////////////////////////////////////////////////////////////*/

    /**
     * @dev Classifies one node, given its children (already classified:
     *      they have higher indices).
     *
     *      The evaluator finds every value from the tree alone: a node's
     *      encoding and its children's say where in calldata its children
     *      are read. So every node must describe the ABI type of the value
     *      it is evaluated at, and nodes that are evaluated at the same
     *      value must agree on it.
     */
    function _type(Node[] memory nodes, uint256 index) private pure {
        Node memory node = nodes[index];
        Encoding encoding = node.encoding;
        Operator op = node.operator;

        bool navigates = _navigates(op);
        bool isLogical = op == Operator.And || op == Operator.Or;
        bool isContainer = encoding == Encoding.Tuple ||
            encoding == Encoding.Array ||
            encoding == Encoding.AbiEncoded;
        // A node that reads no calldata where it sits: the ether value,
        // allowances, a Zip, ...
        bool readsNothing = (encoding == Encoding.None ||
            encoding == Encoding.EtherValue) && !isLogical;

        Children memory children = _children(nodes, index);
        node.exact = op == Operator.Pass && children.allExact;
        node.rootOk =
            encoding == Encoding.AbiEncoded ||
            (isLogical && children.allRoots);

        /*
         * The root is evaluated at the calldata itself: it is AbiEncoded,
         * an And / Or over such nodes (and nodes that are evaluated nowhere
         * in particular), or a leaf that reads no calldata.
         */
        if (index == 0 && !node.rootOk && !readsNothing) {
            revert IEvaluatorError.UnsuitableRootNode();
        }

        if (readsNothing) {
            node.kind = NON_STRUCTURAL;
        } else if (encoding == Encoding.Static) {
            node.kind = STATIC;
        } else if (encoding == Encoding.Dynamic) {
            node.kind = DYNAMIC;
        } else if (isContainer) {
            /*
             * A container describes one parameter per child, so a child
             * that reads no calldata has no place in it. A Tuple or Array
             * has at least one; AbiEncoded may have no parameters.
             */
            if (
                (node.childCount == 0 && encoding != Encoding.AbiEncoded) ||
                !children.allTypes
            ) {
                revert IEvaluatorError.UnsuitableChildCount(index);
            }

            // An Array read as a whole is described by its element type
            // alone: its first child. Any other child would never be read
            if (
                encoding == Encoding.Array &&
                !navigates &&
                node.childCount != 1
            ) {
                revert IEvaluatorError.UnsuitableChildCount(index);
            }

            // Non-navigating containers never evaluate their children; they
            // only describe the ABI type, so the subtree must be Pass nodes.
            if (!navigates && !children.allExact) {
                revert IEvaluatorError.UnsuitableChildTypeTree(index);
            }

            node.kind = TYPE_OF + index;
            if (encoding == Encoding.Tuple) {
                node.staticType = children.allStatic;
            } else if (encoding == Encoding.Array) {
                node.element = _elementType(nodes, index);
            }
        } else {
            node.kind = _logicalKind(nodes, index);
        }
    }

    /// @dev What the types pass needs to know about the children of a node.
    struct Children {
        /// All are plain type descriptions
        bool allExact;
        /// All have a type of fixed size
        bool allStatic;
        /// All describe a value: none reads no calldata
        bool allTypes;
        /// All may sit below a root And / Or
        bool allRoots;
    }

    function _children(
        Node[] memory nodes,
        uint256 index
    ) private pure returns (Children memory children) {
        Node memory node = nodes[index];
        children.allExact = true;
        children.allStatic = true;
        children.allTypes = true;
        children.allRoots = true;
        for (uint256 i; i < node.childCount; ++i) {
            Node memory child = nodes[node.childStart + i];
            if (!child.exact) children.allExact = false;
            if (!_isStatic(nodes, child.kind)) children.allStatic = false;
            if (child.kind < STATIC) children.allTypes = false;
            // Below a root And / Or: another root, or a node that is
            // evaluated nowhere in particular
            if (!child.rootOk && child.kind >= STATIC) {
                children.allRoots = false;
            }
        }
    }

    /**
     * @dev The element type of an Array node. Its first child is the
     *      template the evaluator decodes every element with, so it must be
     *      the most specific: every element it types, the others type too.
     */
    function _elementType(
        Node[] memory nodes,
        uint256 index
    ) private pure returns (uint256 element) {
        Node memory node = nodes[index];
        element = nodes[node.childStart].kind;

        for (uint256 i = 1; i < node.childCount; ++i) {
            uint256 other = nodes[node.childStart + i].kind;
            if (!_isSubtype(nodes, element, other)) {
                revert IEvaluatorError.UnsuitableChildTypeTree(index);
            }
        }
    }

    /**
     * @dev What an And / Or is. Its children are all evaluated at the value
     *      it sits at.
     *
     *      - If none reads calldata, neither does the node.
     *      - Otherwise its type is that of the most specific child: one
     *        whose every value the other children type too (checks of
     *        different prefixes of one tuple).
     */
    function _logicalKind(
        Node[] memory nodes,
        uint256 index
    ) private pure returns (uint256) {
        Node memory node = nodes[index];
        uint256 start = node.childStart;
        uint256 end = start + node.childCount;

        uint256 result;
        for (uint256 i = start; i < end && result == 0; ++i) {
            uint256 candidate = nodes[i].kind;
            if (candidate < STATIC) continue;

            bool fits = true;
            for (uint256 j = start; j < end && fits; ++j) {
                uint256 other = nodes[j].kind;
                fits = other < STATIC || _isSubtype(nodes, candidate, other);
            }
            if (fits) result = candidate;
        }
        if (result != 0) return result;

        // No child reads calldata
        for (uint256 i = start; i < end; ++i) {
            if (nodes[i].kind >= STATIC) {
                revert IEvaluatorError.UnsuitableChildTypeTree(index);
            }
        }
        return NON_STRUCTURAL;
    }

    /**
     * @dev A Zip evaluates field i of its Tuple child at every element of
     *      the array in slot i: the field must type every value of that
     *      array's element type. Runs after all nodes are classified, as
     *      the Pluck may sit anywhere in the tree.
     */
    function _zipTypes(
        ConditionFlat[] memory conditions,
        Node[] memory nodes,
        uint256[] memory plucks
    ) private pure {
        for (uint256 i; i < nodes.length; ++i) {
            Node memory node = nodes[i];
            if (!_isZip(node.operator)) continue;

            bytes memory compValue = conditions[i].compValue;
            uint256 fieldStart = nodes[node.childStart].childStart;
            for (uint256 j; j < compValue.length; ++j) {
                Node memory pluck = nodes[plucks[uint8(compValue[j])] - 1];
                uint256 element = nodes[pluck.childStart].kind;
                uint256 field = nodes[fieldStart + j].kind;
                if (!_isSubtype(nodes, element, field)) {
                    revert IEvaluatorError.UnsuitableChildTypeTree(i);
                }
            }
        }
    }

    /**
     * @dev Whether every value of type `a` is also a value of type `b`, so
     *      that a node of type `b` can be evaluated where `a` is expected.
     */
    function _isSubtype(
        Node[] memory nodes,
        uint256 a,
        uint256 b
    ) private pure returns (bool) {
        if (a == STATIC || b == STATIC) return a == b;

        // Bytes and nested calldata are one type, read in different ways
        bool bytesA = _isBytes(nodes, a);
        bool bytesB = _isBytes(nodes, b);
        if (bytesA || bytesB) return bytesA && bytesB;

        Node memory x = nodes[a - TYPE_OF];
        Node memory y = nodes[b - TYPE_OF];
        if (x.encoding != y.encoding) return false;

        if (x.encoding == Encoding.Array) {
            return _isSubtype(nodes, x.element, y.element);
        }

        /*
         * A static tuple is read in place, with exactly the fields listed,
         * whether it is open or not: `a` has as many fields, each fitting.
         */
        if (y.staticType) {
            return x.childCount == y.childCount && _isPrefix(nodes, x, y);
        }

        if (y.operator != Operator.Matches) {
            // A full description: the same fields, none left out
            return
                x.operator != Operator.Matches &&
                x.childCount == y.childCount &&
                _isPrefix(nodes, x, y);
        }

        // Otherwise it types its first fields only, and `a` may have more
        return x.childCount >= y.childCount && _isPrefix(nodes, x, y);
    }

    /// @dev Whether the first fields of tuple `x` are subtypes of the fields
    ///      of tuple `y`.
    function _isPrefix(
        Node[] memory nodes,
        Node memory x,
        Node memory y
    ) private pure returns (bool) {
        for (uint256 i; i < y.childCount; ++i) {
            uint256 a = nodes[x.childStart + i].kind;
            uint256 b = nodes[y.childStart + i].kind;
            if (!_isSubtype(nodes, a, b)) return false;
        }
        return true;
    }

    function _isStatic(
        Node[] memory nodes,
        uint256 kind
    ) private pure returns (bool) {
        return
            kind == STATIC ||
            (kind >= TYPE_OF && nodes[kind - TYPE_OF].staticType);
    }

    function _isBytes(
        Node[] memory nodes,
        uint256 kind
    ) private pure returns (bool) {
        return
            kind == DYNAMIC ||
            (kind >= TYPE_OF &&
                nodes[kind - TYPE_OF].encoding == Encoding.AbiEncoded);
    }

    /*//////////////////////////////////////////////////////////////
                              5. SLOTS
    //////////////////////////////////////////////////////////////*/

    /**
     * @notice Walks a subtree and returns the set of Pluck slots guaranteed
     *         to hold a value once that subtree evaluates successfully.
     *         Reverts if an operator reads a slot (WithinRatio, ZipSome,
     *         ZipEvery) that may still be empty at that point.
     *
     * @dev A slot is only "guaranteed" if every evaluation path that leads
     *      to success fills it:
     *      - And/Matches run children in order, so each child sees the slots
     *        filled by its predecessors, and its own additions carry forward.
     *      - Or: any single branch may be the one that succeeded, so only
     *        slots filled by every branch are guaranteed.
     *      - Some succeeds only if at least one element was actually
     *        evaluated, so its child's assignments count.
     *      - Every passes trivially on an empty collection — its child may
     *        never run, so nothing it assigns can be counted on.
     *      - Zip runs its fields in order at every step, so a field sees the
     *        slots filled by the fields before it. What outlives the Zip
     *        follows Some and Every: the fields of the passing step for
     *        ZipSome, nothing for ZipEvery.
     *      Children of Pass, Pluck, comparisons, and Custom only describe
     *      types and are never evaluated, so they are skipped.
     */
    function _slots(
        ConditionFlat[] memory conditions,
        Node[] memory nodes,
        uint256 index,
        uint256 assigned
    ) private pure returns (uint256) {
        Node memory node = nodes[index];
        Operator op = node.operator;
        bytes memory compValue = conditions[index].compValue;
        uint256 start = node.childStart;
        uint256 end = start + node.childCount;

        if (op == Operator.Pluck) {
            return assigned | (1 << uint8(compValue[0]));
        }

        if (op == Operator.WithinRatio) {
            _requireAssigned(assigned, uint8(compValue[0]), index);
            _requireAssigned(assigned, uint8(compValue[2]), index);
            return assigned;
        }

        if (op == Operator.ZipSome || op == Operator.ZipEvery) {
            for (uint256 i; i < compValue.length; ++i) {
                _requireAssigned(assigned, uint8(compValue[i]), index);
            }
            // The fields, children of the Tuple child, run in order
            Node memory fields = nodes[start];
            uint256 result = assigned;
            for (uint256 i; i < fields.childCount; ++i) {
                result = _slots(
                    conditions,
                    nodes,
                    fields.childStart + i,
                    result
                );
            }
            return op == Operator.ZipSome ? result : assigned;
        }

        if (op == Operator.Or) {
            uint256 intersection = type(uint256).max;
            for (uint256 i = start; i < end; ++i) {
                intersection &= _slots(conditions, nodes, i, assigned);
            }
            return intersection;
        }

        if (op == Operator.ArraySome || op == Operator.ArrayEvery) {
            uint256 result = _slots(conditions, nodes, start, assigned);
            return op == Operator.ArraySome ? result : assigned;
        }

        if (
            op == Operator.And ||
            op == Operator.Matches ||
            op == Operator.ArrayTailMatches
        ) {
            for (uint256 i = start; i < end; ++i) {
                assigned = _slots(conditions, nodes, i, assigned);
            }
            return assigned;
        }

        if (op == Operator.Slice) {
            return _slots(conditions, nodes, start, assigned);
        }

        return assigned;
    }

    /*//////////////////////////////////////////////////////////////
                              HELPERS
    //////////////////////////////////////////////////////////////*/

    /// @dev Operators that evaluate their children at parts of the value
    ///      they sit at, instead of reading it as a whole.
    function _navigates(Operator op) private pure returns (bool) {
        return
            op == Operator.And ||
            op == Operator.Or ||
            op == Operator.Matches ||
            op == Operator.ArraySome ||
            op == Operator.ArrayEvery ||
            op == Operator.ArrayTailMatches ||
            op == Operator.Slice ||
            op == Operator.ZipSome ||
            op == Operator.ZipEvery;
    }

    function _isZip(Operator op) private pure returns (bool) {
        return op == Operator.ZipSome || op == Operator.ZipEvery;
    }

    /// @dev The big-endian uint32 at `offset`.
    function _uint32(
        bytes memory buffer,
        uint256 offset
    ) private pure returns (uint256 result) {
        for (uint256 i; i < 4; ++i) {
            result = (result << 8) | uint8(buffer[offset + i]);
        }
    }

    function _decodeEncoding(
        uint8 raw,
        uint256 index
    ) private pure returns (Encoding) {
        if (raw > uint8(type(Encoding).max)) {
            revert IEvaluatorError.UnsuitableParameterType(index);
        }
        return Encoding(raw);
    }

    function _decodeOperator(
        uint8 raw,
        uint256 index
    ) private pure returns (Operator) {
        if (raw > uint8(type(Operator).max)) {
            revert IEvaluatorError.UnsupportedOperator(index);
        }
        return Operator(raw);
    }

    function _isWord(Encoding encoding) private pure returns (bool) {
        return encoding == Encoding.Static || encoding == Encoding.EtherValue;
    }

    function _requireEncoding(bool suitable, uint256 index) private pure {
        if (!suitable) revert IEvaluatorError.UnsuitableParameterType(index);
    }

    function _requireCompValue(bool suitable, uint256 index) private pure {
        if (!suitable) revert IEvaluatorError.UnsuitableCompValue(index);
    }

    function _requireNoCompValue(
        bytes memory compValue,
        uint256 index
    ) private pure {
        if (compValue.length != 0)
            revert IEvaluatorError.UnsuitableCompValue(index);
    }

    function _requireNoChildren(Node memory node, uint256 index) private pure {
        if (node.childCount != 0) {
            revert IEvaluatorError.LeafNodeCannotHaveChildren(index);
        }
    }

    function _requireAssigned(
        uint256 assigned,
        uint8 slot,
        uint256 index
    ) private pure {
        if ((assigned & (1 << slot)) == 0) {
            revert IEvaluatorError.PluckNotVisitedBeforeRef(index, slot);
        }
    }
}
