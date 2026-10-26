// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "./Topology.sol";
import "./TypeTree.sol";

import "../../types/Types.sol";

/**
 * @title Integrity
 * @notice A library that validates input condition integrity
 *
 * @author gnosisguild
 */
library Integrity {
    uint256 private constant MAX_CONDITION_COUNT = type(uint16).max;
    uint256 private constant MAX_CHILD_COUNT = (1 << 10) - 1;
    uint256 private constant MAX_INLINED_SIZE = (1 << 13) - 1;
    uint256 private constant MAX_COMP_VALUE_LENGTH = type(uint16).max;

    function enforce(ConditionFlat[] memory conditions) internal pure {
        if (conditions.length > MAX_CONDITION_COUNT) {
            revert IRolesError.ConditionNodeCountExceedsMax();
        }

        _validateBFS(conditions);

        for (uint256 i = 0; i < conditions.length; ++i) {
            _validatePackedWidths(conditions, i);
            _validateOperator(conditions, i);
            _validateEncoding(conditions, i);
        }

        _validateVariantTypes(conditions);
        _validatePluckZipTypes(conditions);
        _validateUniquePluckDefinitions(conditions);
        _validatePluckAssignments(conditions, 0, 0);
    }

    function _validatePackedWidths(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        if (conditions[index].compValue.length > MAX_COMP_VALUE_LENGTH) {
            revert IRolesError.UnsuitableCompValue(index);
        }

        (, uint256 childCount) = Topology.childBounds(conditions, index);
        if (childCount > MAX_CHILD_COUNT) {
            revert IRolesError.ConditionChildCountExceedsMax(index);
        }

        if (
            Topology.isInlined(conditions, index) &&
            Topology.inlinedSize(conditions, index) > MAX_INLINED_SIZE
        ) {
            revert IRolesError.ConditionInlinedSizeExceedsMax(index);
        }
    }

    function _validateBFS(ConditionFlat[] memory conditions) private pure {
        uint256 length = conditions.length;
        if (length == 0 || conditions[0].parent != 0) {
            revert IRolesError.UnsuitableRootNode();
        }

        for (uint256 i = 1; i < length; ++i) {
            uint256 parent = conditions[i].parent;
            if (parent == i) {
                revert IRolesError.UnsuitableRootNode();
            }
            // Parent must have lower index (no forward references)
            if (parent < conditions[i - 1].parent) {
                revert IRolesError.NotBFS();
            }
            // Parent cannot be higher than self
            if (parent >= i) {
                revert IRolesError.NotBFS();
            }
        }
    }

    function _validateOperator(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        Operator op = conditions[index].operator;

        if (op == Operator.Pass) {
            _checkPass(conditions, index);
        } else if (op == Operator.And || op == Operator.Or) {
            _checkLogic(conditions, index);
        } else if (op == Operator.Empty) {
            _checkEmpty(conditions, index);
        } else if (op == Operator.Matches) {
            _checkMatches(conditions, index);
        } else if (op == Operator.ArraySome || op == Operator.ArrayEvery) {
            _checkArrayIterator(conditions, index);
        } else if (op == Operator.ArrayTailMatches) {
            _checkArrayTail(conditions, index);
        } else if (op == Operator.ZipSome || op == Operator.ZipEvery) {
            _checkZipIterator(conditions, index);
        } else if (op == Operator.Slice) {
            _checkSlice(conditions, index);
        } else if (op == Operator.Pluck) {
            _checkPluck(conditions, index);
        } else if (op == Operator.EqualToAvatar) {
            _checkEqualToAvatar(conditions, index);
        } else if (op == Operator.EqualTo) {
            _checkEqualTo(conditions, index);
        } else if (
            op == Operator.GreaterThan ||
            op == Operator.LessThan ||
            op == Operator.SignedIntGreaterThan ||
            op == Operator.SignedIntLessThan
        ) {
            _checkComparison(conditions, index);
        } else if (op == Operator.Bitmask) {
            _checkBitmask(conditions, index);
        } else if (op == Operator.Custom) {
            _checkCustom(conditions, index);
        } else if (op == Operator.WithinRatio) {
            _checkWithinRatio(conditions, index);
        } else if (op == Operator.WithinAllowance) {
            _checkWithinAllowance(conditions, index);
        } else if (op == Operator.CallWithinAllowance) {
            _checkCallWithinAllowance(conditions, index);
        } else {
            revert IRolesError.UnsupportedOperator(index);
        }
    }

    /**
     * @notice Validates child constraints based on encoding type.
     *
     * @dev Encoding types determine fundamental child rules:
     *      - Leaf types (Static, Dynamic, EtherValue): Cannot have children
     *      - Container types (Tuple, Array): Must have structural children
     *      - None: Operator-dependent (validated elsewhere)
     *
     *      Exception: Slice operator uses Static/Dynamic encoding but requires
     *      exactly one child (validated in _checkSlice).
     */
    function _validateEncoding(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        Encoding encoding = condition.paramType;

        (, uint256 childCount, uint256 sChildCount) = _sChildBounds(
            conditions,
            index
        );

        if (
            (encoding == Encoding.Static ||
                encoding == Encoding.Dynamic ||
                encoding == Encoding.EtherValue) &&
            (condition.operator != Operator.Slice)
        ) {
            // Slice is a special case: uses Static/Dynamic but requires a child
            // Leaf types cannot have children
            if (childCount != 0) {
                revert IRolesError.LeafNodeCannotHaveChildren(index);
            }
        }

        if (
            encoding == Encoding.AbiEncoded ||
            encoding == Encoding.Tuple ||
            encoding == Encoding.Array
        ) {
            // Container types must have structural children for type tree
            if (sChildCount == 0) {
                revert IRolesError.UnsuitableChildCount(index);
            }
        }
    }

    // --- Operator Handlers ---

    function _checkPass(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        // Encoding: Any
        // CompValue: Must be empty
        if (condition.compValue.length != 0) {
            revert IRolesError.UnsuitableCompValue(index);
        }
    }

    function _checkLogic(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        // And/Or
        // ParamType: None
        if (condition.paramType != Encoding.None) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: Empty
        if (condition.compValue.length != 0) {
            revert IRolesError.UnsuitableCompValue(index);
        }
        // Children: Must have children
        (, uint256 childCount) = Topology.childBounds(conditions, index);
        if (childCount == 0) {
            revert IRolesError.UnsuitableChildCount(index);
        }
    }

    function _checkEmpty(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        // ParamType: None
        if (condition.paramType != Encoding.None) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: Empty
        if (condition.compValue.length != 0) {
            revert IRolesError.UnsuitableCompValue(index);
        }
        // Children: None
        (, uint256 childCount) = Topology.childBounds(conditions, index);
        if (childCount != 0) {
            revert IRolesError.LeafNodeCannotHaveChildren(index);
        }
    }

    function _checkMatches(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        Encoding encoding = condition.paramType;
        // ParamType: Tuple, Array, AbiEncoded
        if (
            encoding != Encoding.Tuple &&
            encoding != Encoding.Array &&
            encoding != Encoding.AbiEncoded
        ) {
            revert IRolesError.UnsuitableParameterType(index);
        }

        // CompValue Validation
        if (encoding == Encoding.AbiEncoded) {
            uint16 leadingBytes = condition.compValue.length >= 2
                ? uint16(bytes2(condition.compValue))
                : 0;
            bool valid = condition.compValue.length == 0 ||
                condition.compValue.length == 2 ||
                (condition.compValue.length == 2 + leadingBytes &&
                    leadingBytes <= 32);
            if (!valid) {
                revert IRolesError.UnsuitableCompValue(index);
            }
        } else {
            if (condition.compValue.length != 0) {
                revert IRolesError.UnsuitableCompValue(index);
            }
        }

        // All children must be structural
        (, uint256 childCount, uint256 sChildCount) = _sChildBounds(
            conditions,
            index
        );
        if (sChildCount == 0 || childCount != sChildCount) {
            revert IRolesError.UnsuitableChildCount(index);
        }
    }

    function _checkArrayIterator(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        // ArraySome / ArrayEvery
        // ParamType: Array
        if (condition.paramType != Encoding.Array) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: Empty
        if (condition.compValue.length != 0) {
            revert IRolesError.UnsuitableCompValue(index);
        }
        // Children: Exactly 1 child
        (, uint256 childCount, uint256 sChildCount) = _sChildBounds(
            conditions,
            index
        );
        if (sChildCount != 1 || sChildCount != childCount) {
            revert IRolesError.UnsuitableChildCount(index);
        }
    }

    function _checkArrayTail(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        // ArrayTailMatches
        // ParamType: Array
        if (condition.paramType != Encoding.Array) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: Empty
        if (condition.compValue.length != 0) {
            revert IRolesError.UnsuitableCompValue(index);
        }
        // Children: All children must be structural
        (, uint256 childCount, uint256 sChildCount) = _sChildBounds(
            conditions,
            index
        );
        if (sChildCount == 0 || childCount != sChildCount) {
            revert IRolesError.UnsuitableChildCount(index);
        }
    }

    function _checkZipIterator(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        // ZipSome / ZipEvery
        // ParamType: None
        if (condition.paramType != Encoding.None) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: at least 2 bytes (one per plucked array)
        if (condition.compValue.length < 2) {
            revert IRolesError.UnsuitableCompValue(index);
        }

        // Children: Exactly 1 child
        (
            uint256 childStart,
            uint256 childCount,
            uint256 sChildCount
        ) = _sChildBounds(conditions, index);
        if (sChildCount != 1 || sChildCount != childCount) {
            revert IRolesError.UnsuitableChildCount(index);
        }

        if (conditions[childStart].paramType != Encoding.Tuple) {
            revert IRolesError.UnsuitableChildTypeTree(index);
        }

        /*
         * All children of the Tuple must be structural. TypeTree counts only
         * structural children when matching the field count against compValue,
         * but the evaluator iterates the raw child list - a non-structural
         * child would desync the two and read compValue out of bounds at
         * evaluation time.
         */
        (, uint256 tupleChildCount, uint256 tupleSChildCount) = _sChildBounds(
            conditions,
            childStart
        );
        if (tupleChildCount != tupleSChildCount) {
            revert IRolesError.UnsuitableChildCount(childStart);
        }

        // Child must resolve to a Tuple
        Layout memory layout = TypeTree.resolve(conditions, childStart);
        assert(layout.encoding == Encoding.Tuple);

        // Tuple field count must match compValue length
        if (layout.children.length != condition.compValue.length) {
            revert IRolesError.UnsuitableCompValue(index);
        }

        // Validate pluck references: no duplicates, each must exist and be Array
        uint256 seen;
        for (uint256 k = 0; k < condition.compValue.length; ++k) {
            uint8 pluckIndex = uint8(condition.compValue[k]);
            uint256 mask = 1 << pluckIndex;
            if ((seen & mask) != 0) {
                revert IRolesError.UnsuitableCompValue(index);
            }
            seen |= mask;

            (bool found, uint256 pluckCondition) = _findPluck(
                conditions,
                pluckIndex
            );
            if (
                !found || conditions[pluckCondition].paramType != Encoding.Array
            ) {
                revert IRolesError.UnsuitableCompValue(index);
            }
        }

        // No Pluck allowed in zip descendants
        _validateNoPluckDescendant(conditions, childStart);
    }

    function _checkSlice(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        Encoding encoding = condition.paramType;
        // ParamType: Static / Dynamic
        if (encoding != Encoding.Static && encoding != Encoding.Dynamic) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: 3 bytes
        if (condition.compValue.length != 3) {
            revert IRolesError.UnsuitableCompValue(index);
        }
        uint8 size = uint8(condition.compValue[2]);
        if (size == 0 || size > 32) {
            revert IRolesError.UnsuitableCompValue(index);
        }

        (uint256 childStart, uint256 childCount) = Topology.childBounds(
            conditions,
            index
        );
        // Children: Exactly 1 child
        if (childCount != 1) {
            revert IRolesError.UnsuitableChildCount(index);
        }

        // The child must resolve to Static
        if (conditions[childStart].paramType != Encoding.Static) {
            revert IRolesError.SliceChildNotStatic(index);
        }
    }

    function _checkPluck(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        Encoding encoding = condition.paramType;
        // ParamType: Static / EtherValue / Array
        if (
            encoding != Encoding.Static &&
            encoding != Encoding.EtherValue &&
            encoding != Encoding.Array
        ) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: 1 byte holding the pluck slot index. The packed buffer
        // header stores `maxPluckCount = max(pluckIndex) + 1` in 8 bits, so
        // index 255 would overflow that field on pack. Capped at 254 here.
        if (
            condition.compValue.length != 1 ||
            uint8(condition.compValue[0]) == 255
        ) {
            revert IRolesError.UnsuitableCompValue(index);
        }

        if (encoding == Encoding.Array) {
            /*
             * All children of an Array Pluck must be structural. They only
             * describe the element type and are never evaluated, but the
             * evaluator reads the raw children[0] as the element template
             * for location and size math - a non-structural child is
             * invisible to TypeTree yet breaks that traversal.
             */
            (, uint256 childCount, uint256 sChildCount) = _sChildBounds(
                conditions,
                index
            );
            if (childCount != sChildCount) {
                revert IRolesError.UnsuitableChildCount(index);
            }
        }
    }

    function _checkEqualToAvatar(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        // ParamType: Static
        if (condition.paramType != Encoding.Static) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: Empty
        if (condition.compValue.length != 0) {
            revert IRolesError.UnsuitableCompValue(index);
        }
    }

    function _checkEqualTo(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        Encoding enc = condition.paramType;
        // ParamType: Static, Dynamic, Tuple, Array, EtherValue
        if (enc == Encoding.None || enc == Encoding.AbiEncoded) {
            revert IRolesError.UnsuitableParameterType(index);
        }

        // CompValue check
        bool unsuitable;
        if (enc == Encoding.Static || enc == Encoding.EtherValue) {
            unsuitable = condition.compValue.length != 32;
        }

        if (enc == Encoding.Dynamic) {
            unsuitable =
                condition.compValue.length < 64 ||
                condition.compValue.length > MAX_COMP_VALUE_LENGTH;
        }

        if (enc == Encoding.Tuple || enc == Encoding.Array) {
            uint256 minimumLength = Topology.isInlined(conditions, index)
                ? 32
                : 64;
            unsuitable =
                condition.compValue.length < minimumLength ||
                condition.compValue.length > MAX_COMP_VALUE_LENGTH;
        }

        if (unsuitable) {
            revert IRolesError.UnsuitableCompValue(index);
        }
    }

    function _checkComparison(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        Encoding encoding = condition.paramType;
        // ParamType: WordLike
        if (encoding != Encoding.Static && encoding != Encoding.EtherValue) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: 32 bytes
        if (condition.compValue.length != 32) {
            revert IRolesError.UnsuitableCompValue(index);
        }
    }

    function _checkBitmask(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        Encoding encoding = condition.paramType;
        // ParamType: Static / Dynamic
        if (encoding != Encoding.Static && encoding != Encoding.Dynamic) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: 2 shift + 2N
        if (
            condition.compValue.length < 4 ||
            condition.compValue.length > MAX_COMP_VALUE_LENGTH ||
            (condition.compValue.length - 2) % 2 != 0
        ) {
            revert IRolesError.UnsuitableCompValue(index);
        }
    }

    function _checkCustom(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        if (
            condition.paramType != Encoding.Static &&
            condition.paramType != Encoding.Dynamic &&
            condition.paramType != Encoding.Tuple &&
            condition.paramType != Encoding.Array &&
            condition.paramType != Encoding.EtherValue
        ) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: 20 to 65535 bytes
        if (
            condition.compValue.length < 20 ||
            condition.compValue.length > MAX_COMP_VALUE_LENGTH
        ) {
            revert IRolesError.UnsuitableCompValue(index);
        }
    }

    function _checkWithinRatio(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        // ParamType: None
        if (condition.paramType != Encoding.None) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: 12 base, optionally followed by adapter blobs.
        {
            uint256 len = condition.compValue.length;
            if (len < 12 || len > MAX_COMP_VALUE_LENGTH) {
                revert IRolesError.UnsuitableCompValue(index);
            }
            uint256 offset = 12;
            if (len > offset) {
                offset = _checkAdapterBlob(condition.compValue, offset, index);
            }
            if (len > offset) {
                offset = _checkAdapterBlob(condition.compValue, offset, index);
            }
            if (len != offset) {
                revert IRolesError.UnsuitableCompValue(index);
            }
        }
        if (
            uint8(condition.compValue[1]) > 27 ||
            uint8(condition.compValue[3]) > 27
        ) {
            revert IRolesError.AllowanceDecimalsExceedMax(index);
        }

        for (uint256 offset; offset <= 2; offset += 2) {
            (bool found, uint256 pluckCondition) = _findPluck(
                conditions,
                uint8(condition.compValue[offset])
            );
            if (
                found &&
                conditions[pluckCondition].paramType != Encoding.Static &&
                conditions[pluckCondition].paramType != Encoding.EtherValue
            ) {
                revert IRolesError.WithinRatioTargetNotStatic(index);
            }
        }
        // Check ratio bounds
        uint32 minRatio;
        uint32 maxRatio;
        bytes memory cv = condition.compValue;
        assembly {
            minRatio := shr(224, mload(add(cv, 0x24)))
            maxRatio := shr(224, mload(add(cv, 0x28)))
        }
        if (minRatio == 0 && maxRatio == 0) {
            revert IRolesError.WithinRatioNoRatioProvided(index);
        }
        if (minRatio != 0 && maxRatio != 0 && minRatio > maxRatio) {
            revert IRolesError.WithinRatioMinExceedsMax(index);
        }
        // Children: None
        (, uint256 childCount) = Topology.childBounds(conditions, index);
        if (childCount != 0) {
            revert IRolesError.LeafNodeCannotHaveChildren(index);
        }
    }

    function _checkWithinAllowance(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        Encoding encoding = condition.paramType;
        // ParamType: WordLike
        if (encoding != Encoding.Static && encoding != Encoding.EtherValue) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: 32, 34, or >= 54
        if (
            condition.compValue.length > MAX_COMP_VALUE_LENGTH ||
            (condition.compValue.length != 32 &&
                condition.compValue.length != 34 &&
                condition.compValue.length < 54)
        ) {
            revert IRolesError.UnsuitableCompValue(index);
        }
        if (condition.compValue.length > 32) {
            if (
                uint8(condition.compValue[32]) > 27 ||
                uint8(condition.compValue[33]) > 27
            ) {
                revert IRolesError.AllowanceDecimalsExceedMax(index);
            }
        }
    }

    function _checkCallWithinAllowance(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        ConditionFlat memory condition = conditions[index];
        // ParamType: None
        if (condition.paramType != Encoding.None) {
            revert IRolesError.UnsuitableParameterType(index);
        }
        // CompValue: 32 bytes
        if (condition.compValue.length != 32) {
            revert IRolesError.UnsuitableCompValue(index);
        }
        // Children: None
        (, uint256 childCount) = Topology.childBounds(conditions, index);
        if (childCount != 0) {
            revert IRolesError.LeafNodeCannotHaveChildren(index);
        }
    }

    function _validateVariantTypes(
        ConditionFlat[] memory conditions
    ) private pure {
        for (uint256 i = 0; i < conditions.length; ++i) {
            bool isLogical = conditions[i].operator == Operator.And ||
                conditions[i].operator == Operator.Or;
            bool isArray = conditions[i].paramType == Encoding.Array;
            /*
             * Only Logical or Arrays hold variants
             */
            if (!isLogical && !isArray) continue;

            (uint256 childStart, uint256 childCount) = Topology.childBounds(
                conditions,
                i
            );

            Layout memory prev;
            for (uint256 j = 0; j < childCount; ++j) {
                Layout memory next = TypeTree.resolve(
                    conditions,
                    childStart + j
                );

                if (TypeTree.hash(prev) == 0) prev = next;

                if (TypeTree.hash(next) == 0) continue;

                if (!_isTypeCompatible(prev, next)) {
                    revert IRolesError.UnsuitableChildTypeTree(i);
                }
            }
        }
    }

    function _validatePluckZipTypes(
        ConditionFlat[] memory conditions
    ) private pure {
        for (uint256 i = 0; i < conditions.length; ++i) {
            Operator op = conditions[i].operator;
            if (op != Operator.ZipSome && op != Operator.ZipEvery) continue;

            (uint256 childStart, ) = Topology.childBounds(conditions, i);

            Layout memory tuple = TypeTree.resolve(conditions, childStart);

            for (uint256 j = 0; j < tuple.children.length; ++j) {
                (bool found, uint256 pluckCondition) = _findPluck(
                    conditions,
                    uint8(conditions[i].compValue[j])
                );
                if (!found) {
                    revert IRolesError.UnsuitableCompValue(i);
                }
                Layout memory array = TypeTree.resolve(
                    conditions,
                    pluckCondition
                );

                Layout memory arrayEntry = array.children[0];
                Layout memory tupleField = tuple.children[j];

                if (!_isTypeCompatible(arrayEntry, tupleField)) {
                    revert IRolesError.UnsuitableChildTypeTree(i);
                }
            }
        }
    }

    function _validateUniquePluckDefinitions(
        ConditionFlat[] memory conditions
    ) private pure {
        uint256 defined;
        for (uint256 i; i < conditions.length; ++i) {
            if (conditions[i].operator != Operator.Pluck) continue;

            uint8 pluckIndex = uint8(conditions[i].compValue[0]);
            uint256 mask = 1 << pluckIndex;
            if ((defined & mask) != 0) {
                revert IRolesError.DuplicatePluckIndex(i, pluckIndex);
            }
            defined |= mask;
        }
    }

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
     *      Children of Pass, Pluck, comparisons, and Custom only describe
     *      types and are never evaluated, so they are skipped.
     */
    function _validatePluckAssignments(
        ConditionFlat[] memory conditions,
        uint256 index,
        uint256 assigned
    ) private pure returns (uint256) {
        ConditionFlat memory condition = conditions[index];

        if (condition.operator == Operator.Pluck) {
            uint8 pluckIndex = uint8(condition.compValue[0]);
            return assigned | (1 << pluckIndex);
        }

        if (condition.operator == Operator.WithinRatio) {
            uint8 referencePluckIndex = uint8(condition.compValue[0]);
            if ((assigned & (1 << referencePluckIndex)) == 0) {
                revert IRolesError.PluckNotVisitedBeforeRef(
                    index,
                    referencePluckIndex
                );
            }

            uint8 relativePluckIndex = uint8(condition.compValue[2]);
            if ((assigned & (1 << relativePluckIndex)) == 0) {
                revert IRolesError.PluckNotVisitedBeforeRef(
                    index,
                    relativePluckIndex
                );
            }
        }

        if (
            condition.operator == Operator.ZipSome ||
            condition.operator == Operator.ZipEvery
        ) {
            for (uint256 k; k < condition.compValue.length; ++k) {
                uint8 pluckIndex = uint8(condition.compValue[k]);
                if ((assigned & (1 << pluckIndex)) == 0) {
                    revert IRolesError.PluckNotVisitedBeforeRef(
                        index,
                        pluckIndex
                    );
                }
            }
        }

        Operator op = condition.operator;
        (uint256 childStart, uint256 childCount) = Topology.childBounds(
            conditions,
            index
        );

        if (op == Operator.Or) {
            uint256 intersection;
            for (uint256 i; i < childCount; ++i) {
                uint256 branchAssigned = _validatePluckAssignments(
                    conditions,
                    childStart + i,
                    assigned
                );
                intersection = i == 0
                    ? branchAssigned
                    : intersection & branchAssigned;
            }
            return intersection;
        }

        if (op == Operator.ArraySome || op == Operator.ArrayEvery) {
            uint256 childAssigned = _validatePluckAssignments(
                conditions,
                childStart,
                assigned
            );
            return op == Operator.ArraySome ? childAssigned : assigned;
        }

        if (op == Operator.ZipSome || op == Operator.ZipEvery) {
            (uint256 fieldStart, uint256 fieldCount) = Topology.childBounds(
                conditions,
                childStart
            );
            uint256 fieldAssigned = assigned;
            for (uint256 i; i < fieldCount; ++i) {
                fieldAssigned = _validatePluckAssignments(
                    conditions,
                    fieldStart + i,
                    fieldAssigned
                );
            }
            return op == Operator.ZipSome ? fieldAssigned : assigned;
        }

        if (
            op == Operator.And ||
            op == Operator.Matches ||
            op == Operator.ArrayTailMatches
        ) {
            for (uint256 i; i < childCount; ++i) {
                assigned = _validatePluckAssignments(
                    conditions,
                    childStart + i,
                    assigned
                );
            }
            return assigned;
        }

        if (op == Operator.Slice) {
            return _validatePluckAssignments(conditions, childStart, assigned);
        }

        return assigned;
    }

    function _validateNoPluckDescendant(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure {
        if (conditions[index].operator == Operator.Pluck) {
            revert IRolesError.UnsupportedOperator(index);
        }
        (uint256 childStart, uint256 childCount) = Topology.childBounds(
            conditions,
            index
        );
        for (uint256 i = 0; i < childCount; ++i) {
            _validateNoPluckDescendant(conditions, childStart + i);
        }
    }

    /// @dev Validates an adapter blob at the given offset: blobLen(1) + adapter(20) + params(blobLen - 20).
    ///      blobLen must be 0 (no adapter) or >= 20. Returns the offset after the blob.
    function _checkAdapterBlob(
        bytes memory buffer,
        uint256 offset,
        uint256 index
    ) private pure returns (uint256) {
        uint256 blobLen = uint8(buffer[offset]);
        if (blobLen != 0 && blobLen < 20) {
            revert IRolesError.UnsuitableCompValue(index);
        }
        offset += 1 + blobLen;
        if (offset > buffer.length) {
            revert IRolesError.UnsuitableCompValue(index);
        }
        return offset;
    }

    function _sChildBounds(
        ConditionFlat[] memory conditions,
        uint256 index
    )
        private
        pure
        returns (uint256 childStart, uint256 childCount, uint256 sChildCount)
    {
        (childStart, childCount) = Topology.childBounds(conditions, index);
        for (uint256 i; i < childCount; ++i) {
            if (TypeTree.hash(conditions, childStart + i) != 0) {
                ++sChildCount;
            }
        }
    }

    /**
     * @notice Checks if two layouts are type-compatible: either exact type
     *         hash match, or type equivalence (both resolve to Dynamic or
     *         AbiEncoded).
     */
    function _isTypeCompatible(
        Layout memory a,
        Layout memory b
    ) private pure returns (bool) {
        bytes32 hashA = TypeTree.hash(a);
        assert(hashA != 0);

        bytes32 hashB = TypeTree.hash(b);
        assert(hashB != 0);

        if (hashA == hashB) {
            return true;
        }
        return _isDynamicish(a) && _isDynamicish(b);
    }

    /**
     * @notice Finds the conditions index of the Pluck condition with the given
     *         pluck index.
     */
    function _findPluck(
        ConditionFlat[] memory conditions,
        uint8 pluckIndex
    ) private pure returns (bool found, uint256 conditionIndex) {
        for (uint256 i = 0; i < conditions.length; ++i) {
            if (
                conditions[i].operator == Operator.Pluck &&
                uint8(conditions[i].compValue[0]) == pluckIndex
            ) {
                return (true, i);
            }
        }
    }

    function _isDynamicish(Layout memory layout) private pure returns (bool) {
        /*
         * None on a resolved type tree means a Variant placeholder. Such
         * fields equate to Dynamic
         */
        return
            layout.encoding == Encoding.Dynamic ||
            layout.encoding == Encoding.AbiEncoded ||
            layout.encoding == Encoding.None;
    }
}
