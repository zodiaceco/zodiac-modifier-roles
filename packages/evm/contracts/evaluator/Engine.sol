// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "./AbiLocation.sol";

import "./checkers/BitmaskChecker.sol";
import "./checkers/CustomChecker.sol";
import "./checkers/WithinAllowanceChecker.sol";
import "./checkers/WithinRatioChecker.sol";

import {Consumption, Result} from "../IEvaluator.sol";
import "./types/EvaluatorError.sol";
import "./types/EvaluatorTypes.sol";

/**
 * @title Engine
 * @notice Evaluates a condition tree against transaction calldata, returning
 *         allowance consumptions on pass or a violation on failure.
 *
 * @dev Assumes a tree validated by `Integrity` (valid `compValue` shapes,
 *      child counts, and pluck slots written before read) and does not
 *      re-check it.
 *
 *      Traverses calldata via monotonically narrowed slices (see AbiLocation).
 *      Out-of-bounds or non-canonical calldata returns `CalldataOverflow` so
 *      `Or`, `ArraySome`, and `ZipSome` continue to the next candidate;
 *      unsupported operators and overflows in `WithinRatio` / scaled
 *      `WithinAllowance` revert.
 *
 *      `consumptions` is copy-on-write (failing branches discard updates;
 *      violations carry no consumptions). `context.pluckedValues` and
 *      `context.pluckedLocations` are mutated in place, so writes survive
 *      failing branches.
 *
 *      Violations: `And`, `Matches`, and `ArrayTailMatches` forward the
 *      failing child's result; `Or`, `ArraySome`, and `ZipSome` report
 *      themselves; `ArrayEvery` and `ZipEvery` replace `status` while keeping
 *      the failing child's `violatedNodeIndex` and `calldataOffset`.
 *
 * @author gnosisguild
 */
library Engine {
    /**
     * @notice Evaluates `condition` against the transaction in `context`.
     * @param condition    Root of the condition tree.
     * @param consumptions Allowances consumed so far (copy-on-write).
     * @param context      Transaction metadata (with `data` packed via
     *                     `AbiLocation.toSpan`) and pre-allocated pluck slots
     *                     (mutated in place).
     * @return             `Status.Ok` with updated `consumptions`, or a
     *                     violation with `violatedNodeIndex` and `calldataOffset`.
     */
    function evaluate(
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) internal view returns (Result memory) {
        return
            _evaluate(
                AbiLocation.fromSpan(context.data),
                condition.inlineSize,
                condition,
                consumptions,
                context
            );
    }

    /**
     * @dev Evaluates one node at `dataSlice` (exact slice when inlined, or
     *      the suffix from the child's offset to the end of its parent when
     *      referenced). `inlineSize` is the fixed byte size of an inlined
     *      operand (`condition.inlineSize` or an enclosing `Slice` window),
     *      or `0` when sized dynamically from calldata.
     */
    function _evaluate(
        bytes calldata dataSlice,
        uint256 inlineSize,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        // Compare as uint256 to avoid per-branch enum range checks.
        // Operators >= EqualTo are leaf checks, splitting dispatch in half;
        // within each half, the most frequent operators come first.
        uint256 operator = uint256(condition.operator);
        Status status;

        if (operator >= uint256(Operator.EqualTo)) {
            if (operator <= uint256(Operator.SignedIntLessThan)) {
                status = _compare(dataSlice, inlineSize, condition, context);
            } else if (operator == uint256(Operator.WithinAllowance)) {
                (bytes32 word, , bool ok) = _read(
                    dataSlice,
                    inlineSize,
                    condition,
                    context
                );
                if (ok) {
                    (status, consumptions) = WithinAllowanceChecker.check(
                        context.core,
                        consumptions,
                        uint256(word),
                        condition.compValue
                    );
                } else {
                    status = Status.CalldataOverflow;
                }
            } else if (operator == uint256(Operator.CallWithinAllowance)) {
                (status, consumptions) = WithinAllowanceChecker.check(
                    context.core,
                    consumptions,
                    1,
                    condition.compValue
                );
            } else if (operator == uint256(Operator.Bitmask)) {
                status = _bitmask(dataSlice, inlineSize, condition);
            } else if (operator == uint256(Operator.Custom)) {
                (status, consumptions) = _custom(
                    dataSlice,
                    inlineSize,
                    condition,
                    consumptions,
                    context
                );
            } else if (operator == uint256(Operator.WithinRatio)) {
                status = WithinRatioChecker.check(
                    condition.compValue,
                    context.pluckedValues
                );
            } else {
                revert IEvaluatorError.UnsupportedOperator(condition.index);
            }
        } else if (operator == uint256(Operator.Pass)) {
            status = Status.Ok;
        } else if (operator == uint256(Operator.Matches)) {
            return _matches(dataSlice, condition, consumptions, context);
        } else if (operator == uint256(Operator.And)) {
            return _and(dataSlice, condition, consumptions, context);
        } else if (operator == uint256(Operator.Or)) {
            return _or(dataSlice, condition, consumptions, context);
        } else if (operator == uint256(Operator.Pluck)) {
            status = _pluck(dataSlice, inlineSize, condition, context);
        } else if (operator == uint256(Operator.Slice)) {
            return
                _slice(dataSlice, inlineSize, condition, consumptions, context);
        } else if (
            operator == uint256(Operator.ArraySome) ||
            operator == uint256(Operator.ArrayEvery)
        ) {
            return _arrayIterator(dataSlice, condition, consumptions, context);
        } else if (operator == uint256(Operator.ArrayTailMatches)) {
            return
                _arrayTailMatches(dataSlice, condition, consumptions, context);
        } else if (
            operator == uint256(Operator.ZipSome) ||
            operator == uint256(Operator.ZipEvery)
        ) {
            return _zipIterator(dataSlice, condition, consumptions, context);
        } else if (operator == uint256(Operator.Empty)) {
            // Checks the whole transaction calldata, not `dataSlice`.
            status = AbiLocation.fromSpan(context.data).length == 0
                ? Status.Ok
                : Status.CalldataNotEmpty;
        } else {
            revert IEvaluatorError.UnsupportedOperator(condition.index);
        }

        if (status != Status.Ok) {
            return _violation(status, dataSlice, condition, context);
        }
        result.consumptions = consumptions;
    }

    /*//////////////////////////////////////////////////////////////
                             NAVIGATION
    //////////////////////////////////////////////////////////////*/

    function _and(
        bytes calldata dataSlice,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        result.consumptions = consumptions;
        for (uint256 i; i < condition.children.length; ++i) {
            result = _evaluate(
                dataSlice,
                condition.children[i].inlineSize,
                condition.children[i],
                result.consumptions,
                context
            );
            if (result.status != 0) {
                return result;
            }
        }
    }

    function _or(
        bytes calldata dataSlice,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        for (uint256 i; i < condition.children.length; ++i) {
            result = _evaluate(
                dataSlice,
                condition.children[i].inlineSize,
                condition.children[i],
                consumptions,
                context
            );
            if (result.status == 0) {
                return result;
            }
        }

        return _violation(Status.OrViolation, dataSlice, condition, context);
    }

    /**
     * @dev Evaluates `condition.children` in order against a container:
     *      - `AbiEncoded`: parameters, after stripping and checking leading bytes
     *      - `Tuple`:      fields
     *      - `Array`:      elements, length must equal `condition.children.length`
     *
     *      Trailing parameters (`AbiEncoded`) may be omitted. A `Tuple` lists
     *      every field.
     */
    function _matches(
        bytes calldata dataSlice,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        bytes calldata body = dataSlice;

        if (condition.encoding == Encoding.AbiEncoded) {
            // Root calldata starts at offset 0 with no length word. Every nested
            // AbiEncoded is length-prefixed `bytes` at offset >= 32 (past its
            // head slot).
            bool ok = true;
            if (AbiLocation.offsetOf(context.data, dataSlice) != 0) {
                (body, ok) = AbiLocation.slice(dataSlice, 0);
            }
            if (!ok || condition.leadingBytes > body.length) {
                return
                    _violation(
                        Status.CalldataOverflow,
                        dataSlice,
                        condition,
                        context
                    );
            }
            dataSlice = body;
            body = body[condition.leadingBytes:];

            bytes memory leading = condition.compValue;
            if (leading.length > 0) {
                // When set, require the payload to start with `leading` (1–32
                // bytes): load both as left-aligned words and shift out
                // trailing bytes.
                uint256 shift = (32 - leading.length) * 8;
                if (bytes32(leading) >> shift != bytes32(dataSlice) >> shift) {
                    return
                        _violation(
                            Status.LeadingBytesNotAMatch,
                            dataSlice,
                            condition,
                            context
                        );
                }
            }
        }

        Span[] memory children;
        {
            bool ok;
            (children, ok) = AbiLocation.children(body, condition);
            if (!ok) {
                return
                    _violation(
                        Status.CalldataOverflow,
                        dataSlice,
                        condition,
                        context
                    );
            }
            if (condition.children.length != children.length) {
                return
                    _violation(
                        Status.ParameterNotAMatch,
                        dataSlice,
                        condition,
                        context
                    );
            }
        }

        result.consumptions = consumptions;
        for (uint256 i; i < children.length; ++i) {
            result = _evaluate(
                AbiLocation.fromSpan(children[i]),
                condition.children[i].inlineSize,
                condition.children[i],
                result.consumptions,
                context
            );
            if (result.status != 0) {
                return result;
            }
        }
    }

    /**
     * @dev `ArrayEvery`: passes iff every element passes (threading
     *      consumptions; vacuous on empty arrays). `ArraySome`: returns the
     *      first passing element (from input consumptions).
     */
    function _arrayIterator(
        bytes calldata dataSlice,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        bool every = condition.operator == Operator.ArrayEvery;

        (Span[] memory children, bool ok) = AbiLocation.children(
            dataSlice,
            condition
        );
        if (!ok) {
            return
                _violation(
                    Status.CalldataOverflow,
                    dataSlice,
                    condition,
                    context
                );
        }

        result.consumptions = consumptions;
        for (uint256 i; i < children.length; ++i) {
            result = _evaluate(
                AbiLocation.fromSpan(children[i]),
                condition.children[0].inlineSize,
                condition.children[0],
                every ? result.consumptions : consumptions,
                context
            );

            if (every) {
                if (result.status != 0) {
                    result.status = uint8(Status.NotEveryArrayElementPasses);
                    return result;
                }
            } else {
                if (result.status == 0) {
                    return result;
                }
            }
        }

        return
            every
                ? result
                : _violation(
                    Status.NoArrayElementPasses,
                    dataSlice,
                    condition,
                    context
                );
    }

    /**
     * @dev Evaluates `condition.children` in order against the array's tail.
     */
    function _arrayTailMatches(
        bytes calldata dataSlice,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        (Span[] memory children, bool ok) = AbiLocation.children(
            dataSlice,
            condition
        );
        if (!ok) {
            return
                _violation(
                    Status.CalldataOverflow,
                    dataSlice,
                    condition,
                    context
                );
        }

        uint256 conditionCount = condition.children.length;
        if (children.length < conditionCount) {
            return
                _violation(
                    Status.ParameterNotAMatch,
                    dataSlice,
                    condition,
                    context
                );
        }
        uint256 tailOffset = children.length - conditionCount;

        result.consumptions = consumptions;
        for (uint256 i; i < conditionCount; ++i) {
            result = _evaluate(
                AbiLocation.fromSpan(children[tailOffset + i]),
                condition.children[i].inlineSize,
                condition.children[i],
                result.consumptions,
                context
            );
            if (result.status != 0) {
                return result;
            }
        }
    }

    /**
     * @dev Walks the plucked arrays in `compValue` in lockstep, evaluating
     *      `condition.children[0].children[f]` on element `i` of array `f`.
     */
    function _zipIterator(
        bytes calldata dataSlice,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        bool every = condition.operator == Operator.ZipEvery;

        (
            Span[][] memory elements,
            uint256 length,
            Status status
        ) = _zipElements(condition, context);
        if (status != Status.Ok) {
            return _violation(status, dataSlice, condition, context);
        }

        Condition[] memory fields = condition.children[0].children;

        result.consumptions = consumptions;
        for (uint256 i; i < length; ++i) {
            // ZipSome: every step starts from the consumptions given
            if (!every) result.consumptions = consumptions;

            for (uint256 f; f < fields.length; ++f) {
                result = _evaluate(
                    AbiLocation.fromSpan(elements[f][i]),
                    fields[f].inlineSize,
                    fields[f],
                    result.consumptions,
                    context
                );
                if (result.status != 0) break;
            }

            if (every) {
                if (result.status != 0) {
                    result.status = uint8(Status.NotEveryZippedElementPasses);
                    return result;
                }
            } else {
                if (result.status == 0) {
                    return result;
                }
            }
        }

        return
            every
                ? result
                : _violation(
                    Status.NoZippedElementPasses,
                    dataSlice,
                    condition,
                    context
                );
    }

    /**
     * @dev Decodes elements of each plucked array within its stored `Span`
     *      and verifies all arrays have equal length.
     */
    function _zipElements(
        Condition memory condition,
        Context memory context
    )
        private
        pure
        returns (Span[][] memory result, uint256 length, Status status)
    {
        bytes memory slots = condition.compValue;
        Condition[] memory fields = condition.children[0].children;

        result = new Span[][](fields.length);
        for (uint256 f; f < fields.length; ++f) {
            (Span[] memory elements, bool ok) = AbiLocation.elements(
                AbiLocation.fromSpan(context.pluckedLocations[uint8(slots[f])]),
                fields[f].inlineSize
            );
            if (!ok) return (result, 0, Status.CalldataOverflow);

            if (f == 0) {
                length = elements.length;
            } else if (elements.length != length) {
                return (result, 0, Status.ZippedArrayLengthMismatch);
            }
            result[f] = elements;
        }
    }

    /*//////////////////////////////////////////////////////////////
                                CHECKS
    //////////////////////////////////////////////////////////////*/

    /**
     * @dev Narrows a `Static` or `Dynamic` unpadded payload to a byte slice
     *      and evaluates its leaf child with `inlineSize = size` (`Integrity`
     *      enforces `Static`/`Dynamic` parent and one leaf child).
     */
    function _slice(
        bytes calldata dataSlice,
        uint256 inlineSize,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory) {
        /*
         * compValue layout (3 bytes):
         * ┌──────────────────────┬──────────────────────┐
         * │ shift (16 bits)      │ size (8 bits)        │
         * └──────────────────────┴──────────────────────┘
         *   - shift: byte offset into the unpadded payload
         *   - size:  slice length in bytes (1–32)
         */
        uint256 shift = uint16(bytes2(condition.compValue));
        uint256 size = uint8(condition.compValue[2]);

        (bytes calldata payload, bool ok) = AbiLocation.slice(
            dataSlice,
            inlineSize
        );
        if (!ok || shift + size > payload.length) {
            return
                _violation(
                    Status.CalldataOverflow,
                    dataSlice,
                    condition,
                    context
                );
        }

        return
            _evaluate(
                payload[shift:shift + size],
                size,
                condition.children[0],
                consumptions,
                context
            );
    }

    /**
     * @dev Stores the operand word and encoding `Span` (`0` for ether value)
     *      in slot `compValue[0]`, mutating `context` in place.
     */
    function _pluck(
        bytes calldata dataSlice,
        uint256 inlineSize,
        Condition memory condition,
        Context memory context
    ) private pure returns (Status) {
        (bytes32 word, bytes calldata operand, bool ok) = _read(
            dataSlice,
            inlineSize,
            condition,
            context
        );
        if (!ok) return Status.CalldataOverflow;

        uint256 slot = uint8(condition.compValue[0]);
        context.pluckedValues[slot] = word;
        context.pluckedLocations[slot] = condition.encoding == Encoding.None
            ? Span.wrap(0)
            : AbiLocation.toSpan(operand);
        return Status.Ok;
    }

    /**
     * @dev Evaluates `EqualTo` (word vs word, or length + `keccak256` above
     *      32 bytes) and unsigned/signed ordering (`SignedInt*` sign-extends
     *      narrow `Slice` windows via `signextend(length - 1, word)`).
     */
    function _compare(
        bytes calldata dataSlice,
        uint256 inlineSize,
        Condition memory condition,
        Context memory context
    ) private pure returns (Status) {
        (bytes32 word, bytes calldata operand, bool ok) = _read(
            dataSlice,
            inlineSize,
            condition,
            context
        );
        if (!ok) return Status.CalldataOverflow;

        uint256 length = condition.encoding == Encoding.None
            ? 32
            : operand.length;
        uint256 operator = uint256(condition.operator);
        bytes memory compValue = condition.compValue;

        if (operator == uint256(Operator.EqualTo)) {
            bool equal = length > 32
                ? compValue.length == length && word == keccak256(compValue)
                : compValue.length == 32 && word == bytes32(compValue);
            return equal ? Status.Ok : Status.ParameterNotAllowed;
        }

        bytes32 bound = bytes32(compValue);
        if (operator == uint256(Operator.GreaterThan)) {
            return word > bound ? Status.Ok : Status.ParameterLessThanAllowed;
        }
        if (operator == uint256(Operator.LessThan)) {
            return
                word < bound ? Status.Ok : Status.ParameterGreaterThanAllowed;
        }

        // Sign-extend windows narrower than 32 bytes from their top bit.
        int256 signedValue;
        assembly {
            signedValue := signextend(sub(length, 1), word)
        }
        int256 signedBound = int256(uint256(bound));
        if (operator == uint256(Operator.SignedIntGreaterThan)) {
            return
                signedValue > signedBound
                    ? Status.Ok
                    : Status.ParameterLessThanAllowed;
        }
        return
            signedValue < signedBound
                ? Status.Ok
                : Status.ParameterGreaterThanAllowed;
    }

    function _bitmask(
        bytes calldata dataSlice,
        uint256 inlineSize,
        Condition memory condition
    ) private pure returns (Status) {
        (bytes calldata payload, bool ok) = AbiLocation.slice(
            dataSlice,
            inlineSize
        );
        if (!ok) return Status.CalldataOverflow;

        return BitmaskChecker.check(payload, condition.compValue);
    }

    /**
     * @dev Calls the `ICustomCondition` adapter with `(location, length)` of
     *      the operand (`slice` when inlined/sliced, `sliceEncoded`
     *      otherwise, or `length = 0` for ether value).
     */
    function _custom(
        bytes calldata dataSlice,
        uint256 inlineSize,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Status, Consumption[] memory) {
        uint256 length;
        if (condition.encoding != Encoding.None) {
            (bytes calldata operand, bool ok) = inlineSize > 0
                ? AbiLocation.slice(dataSlice, inlineSize)
                : AbiLocation.sliceEncoded(dataSlice, condition);
            if (!ok) return (Status.CalldataOverflow, consumptions);
            dataSlice = operand;
            length = operand.length;
        }

        return
            CustomChecker.check(
                condition.compValue,
                AbiLocation.offsetOf(context.data, dataSlice),
                length,
                consumptions,
                context
            );
    }

    /*//////////////////////////////////////////////////////////////
                              OPERANDS
    //////////////////////////////////////////////////////////////*/

    /**
     * @dev Reads an operand as one word: `context.value` for `Encoding.None`,
     *      right-aligned/zero-extended for `<= 32` bytes, or `keccak256` above.
     */
    function _read(
        bytes calldata dataSlice,
        uint256 inlineSize,
        Condition memory condition,
        Context memory context
    ) private pure returns (bytes32 word, bytes calldata operand, bool ok) {
        if (condition.encoding == Encoding.None) {
            return (bytes32(context.value), dataSlice, true);
        }

        // In place when inlined (or below a Slice), otherwise sized from calldata
        (operand, ok) = inlineSize > 0
            ? AbiLocation.slice(dataSlice, inlineSize)
            : AbiLocation.sliceEncoded(dataSlice, condition);
        if (!ok) return (0, dataSlice, false);

        uint256 length = operand.length;
        word = length > 32
            ? keccak256(operand)
            : bytes32(operand) >> ((32 - length) * 8);
    }

    /*//////////////////////////////////////////////////////////////
                              RESULTS
    //////////////////////////////////////////////////////////////*/

    function _violation(
        Status status,
        bytes calldata dataSlice,
        Condition memory condition,
        Context memory context
    ) private pure returns (Result memory result) {
        result.status = uint8(status);
        result.violatedNodeIndex = condition.index;
        result.calldataOffset = AbiLocation.offsetOf(context.data, dataSlice);
    }
}
