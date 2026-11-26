// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Operation} from "@gnosis-guild/zodiac-core/contracts/core/Operation.sol";

enum Encoding {
    None,
    Static,
    Dynamic,
    Tuple,
    Array,
    AbiEncoded,
    /* EtherValue is a nonstructural, and an alias for None */
    EtherValue
}

enum Operator {
    // 00:    EMPTY EXPRESSION (default, always passes)
    //          paramType: Static / Dynamic / Tuple / Array / EtherValue
    //          ❓ children (only for paramType: Tuple / Array to describe their structure)
    //          🚫 compValue
    /* 00: */ Pass,
    // ------------------------------------------------------------
    // 01-03: LOGICAL EXPRESSIONS
    //          paramType: None
    //          ✅ children
    //          🚫 compValue
    /* 01: */ And,
    /* 02: */ Or,
    /* 03: */ _Placeholder03,
    // ------------------------------------------------------------
    // 04:    EMPTY CHECK (passes if data.length == 0)
    //          paramType: None
    //          🚫 children
    //          🚫 compValue
    /* 04: */ Empty,
    // ------------------------------------------------------------
    // 05-12: COMPLEX EXPRESSIONS
    //          paramType: AbiEncoded / Tuple / Array,
    //          ✅ children
    //          🚫 compValue (exception AbiEncoded.Matches uses compValue to define leading bytes)
    /* 05: */ Matches,
    /* 06: */ ArraySome,
    /* 07: */ ArrayEvery,
    /* 08: */ ArrayTailMatches,
    /* 09: */ _Placeholder09,
    /* 10: */ ZipSome, // paramType: None, compValue: at least 1 byte, one per plucked array
    /* 11: */ ZipEvery, // paramType: None, compValue: at least 1 byte, one per plucked array
    /* 12: */ _Placeholder12,
    // ------------------------------------------------------------
    // 13-14: EXTRACTION EXPRESSIONS
    //          ❓ children (at most one child, must resolve to Static)
    //          ✅ compValue
    /* 13: */ Slice, // paramType: Static / Dynamic, compValue: 3 bytes (2 bytes shift + 1 byte size, 1-32)
    /* 14: */ Pluck, // paramType: Static / EtherValue / Array, compValue: 1 byte (index into pluckedValues, 0-254)
    // ------------------------------------------------------------
    // 15:    SPECIAL COMPARISON (without compValue)
    //          paramType: Static
    //          🚫 children
    //          🚫 compValue
    /* 15: */ EqualToAvatar,
    // ------------------------------------------------------------
    // 16-31: COMPARISON EXPRESSIONS
    //          paramType: Static / Dynamic / Tuple / Array / EtherValue
    //          ❓ children (only for paramType: Tuple / Array to describe their structure)
    //          ✅ compValue
    /* 16: */ EqualTo, // paramType: Static / Dynamic / Tuple / Array / EtherValue
    /* 17: */ GreaterThan, // paramType: Static / EtherValue
    /* 18: */ LessThan, // paramType: Static / EtherValue
    /* 19: */ SignedIntGreaterThan, // paramType: Static / EtherValue
    /* 20: */ SignedIntLessThan, // paramType: Static / EtherValue
    /* 21: */ Bitmask, // paramType: Static / Dynamic
    /* 22: */ Custom, // paramType: None / Static / Dynamic / Tuple / Array / EtherValue
    /* 23: */ WithinRatio, // paramType: None
    /* 24: */ _Placeholder24,
    /* 25: */ _Placeholder25,
    /* 26: */ _Placeholder26,
    /* 27: */ _Placeholder27,
    /* 28: */ WithinAllowance, // paramType: Static / EtherValue
    /* 29: */ _Placeholder29,
    /* 30: */ CallWithinAllowance, // paramType: None
    /* 31: */ _Placeholder31
}

enum Status {
    Ok,
    /// Or condition not met
    OrViolation,
    /// Parameter value is not equal to allowed
    ParameterNotAllowed,
    /// Parameter value less than allowed
    ParameterLessThanAllowed,
    /// Parameter value greater than maximum allowed by role
    ParameterGreaterThanAllowed,
    /// Parameter value does not match
    ParameterNotAMatch,
    /// Array elements do not meet allowed criteria for every element
    NotEveryArrayElementPasses,
    /// Array elements do not meet allowed criteria for at least one element
    NoArrayElementPasses,
    /// Bitmask exceeded value length
    BitmaskOverflow,
    /// Bitmask not an allowed value
    BitmaskNotAllowed,
    CustomConditionViolation,
    CustomConditionNotAContract,
    CustomConditionReverted,
    CustomConditionInvalidResult,
    PricingAdapterNotAContract,
    PricingAdapterReverted,
    PricingAdapterInvalidResult,
    PricingAdapterZeroPrice,
    AllowanceExceeded,
    /// No longer emitted: full-precision comparison reports AllowanceExceeded
    /// instead. Kept to preserve status codes.
    AllowanceValueOverflow,
    CalldataOverflow,
    RatioBelowMin,
    RatioAboveMax,
    /// Calldata is not empty when it should be
    CalldataNotEmpty,
    /// Leading bytes do not match expected value
    LeadingBytesNotAMatch,
    /// Zipped arrays have different lengths
    ZippedArrayLengthMismatch,
    /// No zipped element pair passes
    NoZippedElementPasses,
    /// Not every zipped element pair passes
    NotEveryZippedElementPasses
}

struct Condition {
    /// @dev BFS index from unpacking - identifies this node in the flattened tree
    uint256 index;
    Encoding encoding;
    Operator operator;
    bytes compValue;
    Condition[] children;
    /* meta fields */
    uint256 inlineSize;
    uint256 leadingBytes;
}

/// @dev Packed calldata slice (`offset` in low 128 bits, `length` in high 128).
///      Construct via `AbiLocation.toSpan`; `Span.wrap(0)` is an empty slice.
type Span is uint256;

struct Context {
    address core;
    address to;
    uint256 value;
    Span data;
    Operation operation;
    bytes32[] pluckedValues;
    Span[] pluckedLocations;
}
