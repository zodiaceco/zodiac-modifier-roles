// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "./BitmaskChecker.sol";
import "./CustomConditionChecker.sol";
import "./WithinAllowanceChecker.sol";
import "./WithinRatioChecker.sol";

import "../../common/AbiLocation.sol";

import "../../types/Types.sol";

/**
 * @title ConditionEvaluator
 * @notice Evaluates condition trees on scoped function calls.
 * @author gnosisguild
 */
library ConditionEvaluator {
    function evaluate(
        bytes calldata data,
        uint256 location,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) internal view returns (Result memory) {
        Operator operator = condition.operator;

        if (operator < Operator.EqualTo) {
            if (operator == Operator.Pass) {
                return _ok(consumptions);
            } else if (operator == Operator.Matches) {
                location = location > 0 &&
                    condition.encoding == Encoding.AbiEncoded
                    ? location + 32
                    : location;
                return
                    _matches(data, location, condition, consumptions, context);
            } else if (operator == Operator.And) {
                return _and(data, location, condition, consumptions, context);
            } else if (operator == Operator.Or) {
                return _or(data, location, condition, consumptions, context);
            } else if (operator == Operator.Slice) {
                return _slice(data, location, condition, consumptions, context);
            } else if (operator == Operator.Pluck) {
                return _pluck(data, location, condition, consumptions, context);
            } else if (operator == Operator.Empty) {
                return
                    _result(
                        data.length == 0 ? Status.Ok : Status.CalldataNotEmpty,
                        0,
                        condition,
                        consumptions
                    );
            } else if (
                operator == Operator.ArraySome ||
                operator == Operator.ArrayEvery
            ) {
                return
                    _arrayIterator(
                        data,
                        location,
                        condition,
                        consumptions,
                        context
                    );
            } else if (operator == Operator.ArrayTailMatches) {
                return
                    _arrayTailMatches(
                        data,
                        location,
                        condition,
                        consumptions,
                        context
                    );
            } else if (
                operator == Operator.ZipSome || operator == Operator.ZipEvery
            ) {
                return
                    _zipIterator(
                        data,
                        location,
                        condition,
                        consumptions,
                        context
                    );
            }
        } else {
            if (operator <= Operator.SignedIntLessThan) {
                (bytes32 value, bool overflow) = __input(
                    data,
                    location,
                    condition,
                    context
                );

                return
                    _result(
                        overflow
                            ? Status.CalldataOverflow
                            : operator <= Operator.LessThan
                                ? __compare(value, condition)
                                : __compareSigned(value, condition),
                        location,
                        condition,
                        consumptions
                    );
            } else if (operator == Operator.Bitmask) {
                return
                    _result(
                        BitmaskChecker.check(
                            data,
                            location,
                            condition.compValue,
                            condition.inlined,
                            condition.size
                        ),
                        location,
                        condition,
                        consumptions
                    );
            } else if (operator == Operator.WithinAllowance) {
                (bytes32 value, bool overflow) = __input(
                    data,
                    location,
                    condition,
                    context
                );
                if (overflow) {
                    return
                        _violation(
                            Status.CalldataOverflow,
                            location,
                            condition
                        );
                }
                return
                    __allowance(
                        uint256(value),
                        location,
                        condition,
                        consumptions
                    );
            } else if (operator == Operator.CallWithinAllowance) {
                return __allowance(1, location, condition, consumptions);
            } else if (operator == Operator.WithinRatio) {
                return
                    _result(
                        WithinRatioChecker.check(
                            condition.compValue,
                            context.pluckedValues
                        ),
                        location,
                        condition,
                        consumptions
                    );
            } else if (operator == Operator.Custom) {
                uint256 size = condition.size != 0
                    ? condition.size
                    : AbiLocation.size(data, location, condition);
                (
                    Status status,
                    Consumption[] memory nextConsumptions
                ) = CustomConditionChecker.check(
                        condition.compValue,
                        context.to,
                        context.value,
                        data,
                        context.operation,
                        location,
                        size,
                        consumptions,
                        context.pluckedValues
                    );
                return _result(status, location, condition, nextConsumptions);
            }
        }

        revert IRolesError.UnsupportedOperator(condition.index);
    }

    function _matches(
        bytes calldata data,
        uint256 location,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        uint256 length = condition.compValue.length;
        if (length > 0) {
            /*
             * Leading Bytes Validation
             *
             * AbiEncoded + Matches may carry an optional prefix (N <= 32,
             * enforced by Integrity) that must match the first N bytes of
             * calldata at location:
             *
             *   data[location:location + length] == compValue
             *
             * The 2-byte count preceding the prefix in the stored payload is
             * split out by the unpacker into the node's `leadingBytes`, so
             * compValue is exactly the prefix.
             *
             * Both sides are compared on a 32-byte word basis: right-aligned
             * in bytes32, shifting out the trailing 32 - N bytes (shift
             * operands are bits, hence * 8). No slice is allocated.
             */

            // Check bounds before reading leading bytes
            if (location + length > data.length) {
                return _violation(Status.CalldataOverflow, location, condition);
            }

            uint256 shift = (32 - length) * 8;
            bytes32 expected = bytes32(condition.compValue) >> shift;
            bytes32 actual = bytes32(data[location:]) >> shift;

            if (expected != actual) {
                return
                    _violation(
                        Status.LeadingBytesNotAMatch,
                        location,
                        condition
                    );
            }
        }

        // Decode children locations - all children are structural
        (uint256[] memory childLocations, bool overflow) = AbiLocation.children(
            data,
            location + condition.leadingBytes,
            condition
        );

        if (overflow) {
            return _violation(Status.CalldataOverflow, location, condition);
        }

        if (condition.children.length != childLocations.length) {
            return _violation(Status.ParameterNotAMatch, location, condition);
        }

        result.consumptions = consumptions;
        for (uint256 i; i < childLocations.length; ++i) {
            result = evaluate(
                data,
                childLocations[i],
                condition.children[i],
                result.consumptions,
                context
            );
            if (result.status != Status.Ok) {
                return result;
            }
        }
        return result;
    }

    function _and(
        bytes calldata data,
        uint256 location,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        result.consumptions = consumptions;
        for (uint256 i; i < condition.children.length; ++i) {
            result = evaluate(
                data,
                location,
                condition.children[i],
                result.consumptions,
                context
            );
            if (result.status != Status.Ok) {
                return result;
            }
        }
        return result;
    }

    function _or(
        bytes calldata data,
        uint256 location,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        for (uint256 i; i < condition.children.length; ++i) {
            result = evaluate(
                data,
                location,
                condition.children[i],
                consumptions,
                context
            );
            if (result.status == Status.Ok) {
                return result;
            }
        }

        return _violation(Status.OrViolation, location, condition);
    }

    function _arrayIterator(
        bytes calldata data,
        uint256 location,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        bool every = condition.operator == Operator.ArrayEvery;

        (uint256[] memory childLocations, bool overflow) = AbiLocation.children(
            data,
            location,
            condition
        );

        if (overflow) {
            return _violation(Status.CalldataOverflow, location, condition);
        }

        result.consumptions = consumptions;
        for (uint256 i; i < childLocations.length; ++i) {
            result = evaluate(
                data,
                childLocations[i],
                condition.children[0],
                every ? result.consumptions : consumptions,
                context
            );

            if (every) {
                if (result.status != Status.Ok) {
                    result.status = Status.NotEveryArrayElementPasses;
                    return result;
                }
            } else {
                if (result.status == Status.Ok) {
                    return result;
                }
            }
        }

        return
            every
                ? result
                : _violation(Status.NoArrayElementPasses, location, condition);
    }

    function _arrayTailMatches(
        bytes calldata data,
        uint256 location,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        // Decode array element locations
        (uint256[] memory childLocations, bool overflow) = AbiLocation.children(
            data,
            location,
            condition
        );

        if (overflow) {
            return _violation(Status.CalldataOverflow, location, condition);
        }

        uint256 conditionCount = condition.children.length;
        uint256 childCount = childLocations.length;

        if (childCount < conditionCount) {
            return _violation(Status.ParameterNotAMatch, location, condition);
        }

        uint256 tailOffset = childCount - conditionCount;

        result.consumptions = consumptions;
        for (uint256 i; i < conditionCount; ++i) {
            result = evaluate(
                data,
                childLocations[tailOffset + i],
                condition.children[i],
                result.consumptions,
                context
            );

            if (result.status != Status.Ok) {
                return result;
            }
        }
        return result;
    }

    function _zipIterator(
        bytes calldata data,
        uint256 location,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        bool every = condition.operator == Operator.ZipEvery;

        (
            uint256[][] memory locations,
            uint256 length,
            Status status
        ) = _zipLocations(data, condition, context);

        if (status != Status.Ok) {
            return _violation(status, location, condition);
        }

        Condition[] memory fields = condition.children[0].children;

        result.consumptions = consumptions;
        for (uint256 i; i < length; ++i) {
            // For ZipSome, we always start from base consumptions.
            if (!every) result.consumptions = consumptions;

            bool tuplePasses = true;
            for (uint256 f; f < fields.length; ++f) {
                result = evaluate(
                    data,
                    locations[f][i],
                    fields[f],
                    result.consumptions,
                    context
                );
                if (result.status != Status.Ok) {
                    tuplePasses = false;
                    break;
                }
            }

            if (every) {
                if (!tuplePasses) {
                    result.status = Status.NotEveryZippedElementPasses;
                    return result;
                }
            } else {
                if (tuplePasses) {
                    return result;
                }
            }
        }

        return
            every
                ? result
                : _violation(Status.NoZippedElementPasses, location, condition);
    }

    /*
     * Slice computes a new location pointing to a byte-range within the
     * current location, so the child transparently evaluates against that
     * slice.
     *
     * The child will read the slice via __input, which right-aligns values
     * <=32 bytes to match comparison compValue encoding.
     */
    function _slice(
        bytes calldata data,
        uint256 location,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private view returns (Result memory result) {
        /*
         * compValue layout (3 bytes):
         *
         *   ┌──────────────────────┬──────────────────────┐
         *   │ shift (16 bits)      │ size (8 bits)        │
         *   └──────────────────────┴──────────────────────┘
         *
         *   shift  byte offset into the operand content at which the window starts
         *   size   number of bytes to extract (right-aligned into a bytes32 word)
         */
        uint256 shift = uint256(uint16(bytes2(condition.compValue)));
        uint256 size = uint256(uint8(condition.compValue[2]));

        /*
         * Integrity guarantees Slice targets either Static or Dynamic values
         * and has one Static child. Normalize both cases to one byte range:
         * - Static starts at `location` and is bounded by `condition.size`.
         * - Dynamic starts after the length word and is bounded by its
         *   declared byte length, not by ABI padding.
         */
        uint256 length = condition.size;
        if (!condition.inlined) {
            if (location + 32 > data.length) {
                return _violation(Status.CalldataOverflow, location, condition);
            }

            assembly {
                length := calldataload(add(data.offset, location))
            }
        }

        if (shift + size > length) {
            return _violation(Status.CalldataOverflow, location, condition);
        }

        Condition memory sliced = condition.children[0];
        sliced.size = size;

        return
            evaluate(
                data,
                location + (condition.inlined ? 0 : 32) + shift,
                sliced,
                consumptions,
                context
            );
    }

    function _pluck(
        bytes calldata data,
        uint256 location,
        Condition memory condition,
        Consumption[] memory consumptions,
        Context memory context
    ) private pure returns (Result memory) {
        (bytes32 pluckedValue, bool overflow) = __input(
            data,
            location,
            condition,
            context
        );
        if (overflow) {
            return _violation(Status.CalldataOverflow, location, condition);
        }

        uint256 index = uint8(condition.compValue[0]);
        context.pluckedLocations[index] = location;
        context.pluckedValues[index] = pluckedValue;

        return _ok(consumptions);
    }

    function __compare(
        bytes32 value,
        Condition memory condition
    ) private pure returns (Status) {
        bytes32 compValue = condition.compValue.length > 32
            ? keccak256(condition.compValue)
            : bytes32(condition.compValue);

        if (condition.operator == Operator.EqualTo) {
            return value == compValue ? Status.Ok : Status.ParameterNotAllowed;
        }
        if (condition.operator == Operator.GreaterThan) {
            return
                value > compValue ? Status.Ok : Status.ParameterLessThanAllowed;
        }
        return
            value < compValue ? Status.Ok : Status.ParameterGreaterThanAllowed;
    }

    function __compareSigned(
        bytes32 rawValue,
        Condition memory condition
    ) private pure returns (Status) {
        int256 value = int256(uint256(rawValue));
        int256 compValue = int256(uint256(bytes32(condition.compValue)));

        if (condition.operator == Operator.SignedIntGreaterThan) {
            return
                value > compValue ? Status.Ok : Status.ParameterLessThanAllowed;
        }
        return
            value < compValue ? Status.Ok : Status.ParameterGreaterThanAllowed;
    }

    function __allowance(
        uint256 value,
        uint256 location,
        Condition memory condition,
        Consumption[] memory consumptions
    ) private view returns (Result memory) {
        (
            Status status,
            Consumption[] memory nextConsumptions
        ) = WithinAllowanceChecker.check(
                consumptions,
                value,
                condition.compValue
            );

        return _result(status, location, condition, nextConsumptions);
    }

    /**
     * @dev Reads a value from calldata or from Transaction.value, right-aligning when needed.
     *      - Encoding.None: returns context.value (ether amount)
     *      - size <= 32: reads from calldata and right-aligns
     *      - size > 32: returns keccak256 hash of the calldata slice
     *
     * @param data      The calldata to read from.
     * @param location  The location in calldata.
     * @param condition The condition with layout info.
     * @param context   The execution context (for ether value).
     * @return result   The value as bytes32, right-aligned or hashed.
     */
    function __input(
        bytes calldata data,
        uint256 location,
        Condition memory condition,
        Context memory context
    ) private pure returns (bytes32 result, bool overflow) {
        /*
         * Integrity rules map Encoding.EtherValue -> Encoding.None during packing.
         * If we encounter Encoding.None here (in a comparison context), it acts as
         * a virtual static parameter representing the transaction value.
         */
        if (condition.encoding == Encoding.None) {
            return (bytes32(context.value), false);
        }

        // Check if condition has size set (e.g., from Slice), otherwise get from decoder
        uint256 size = condition.size != 0
            ? condition.size
            : AbiLocation.size(data, location, condition);

        if (location + size > data.length) {
            return (0, true);
        }

        if (size == 32) {
            assembly {
                result := calldataload(add(data.offset, location))
            }
            return (result, false);
        }

        // align the word for slicing
        if (size < 32) {
            return (
                bytes32(data[location:location + size]) >> ((32 - size) * 8),
                false
            );
        }

        // size > 32
        return (keccak256(data[location:location + size]), false);
    }

    function _ok(
        Consumption[] memory consumptions
    ) private pure returns (Result memory) {
        return
            Result({
                status: Status.Ok,
                violatedNodeIndex: 0,
                payloadLocation: 0,
                consumptions: consumptions
            });
    }

    function _violation(
        Status status,
        uint256 location,
        Condition memory condition
    ) private pure returns (Result memory) {
        Consumption[] memory empty;
        return
            Result({
                status: status,
                violatedNodeIndex: condition.index,
                payloadLocation: location,
                consumptions: empty
            });
    }

    function _result(
        Status status,
        uint256 location,
        Condition memory condition,
        Consumption[] memory consumptions
    ) private pure returns (Result memory) {
        return
            status == Status.Ok
                ? _ok(consumptions)
                : _violation(status, location, condition);
    }

    /**
     * @dev Resolves element locations for arrays being zipped together.
     *
     * @param data      The calldata being evaluated.
     * @param condition The Zip condition (ZipSome / ZipEvery).
     * @param context   Evaluation context with pluckedLocations.
     *
     * @return result One uint256[] per array – element locations in calldata.
     * @return length The common length of all zipped arrays.
     * @return status Status.Ok, or an error
     */
    function _zipLocations(
        bytes calldata data,
        Condition memory condition,
        Context memory context
    )
        private
        pure
        returns (uint256[][] memory result, uint256 length, Status status)
    {
        Condition[] memory fields = condition.children[0].children;
        Condition memory stub;
        stub.encoding = Encoding.Array;
        stub.children = new Condition[](1);

        result = new uint256[][](fields.length);

        for (uint256 f; f < fields.length; ++f) {
            stub.children[0] = fields[f];
            (uint256[] memory locations, bool overflow) = AbiLocation.children(
                data,
                context.pluckedLocations[uint8(condition.compValue[f])],
                stub
            );

            if (overflow) return (result, 0, Status.CalldataOverflow);

            if (f == 0) {
                length = locations.length;
            } else {
                if (length != locations.length) {
                    return (result, 0, Status.ZippedArrayLengthMismatch);
                }
            }

            result[f] = locations;
        }
    }
}
