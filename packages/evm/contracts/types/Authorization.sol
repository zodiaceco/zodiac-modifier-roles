// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "@gnosis-guild/zodiac-core/contracts/core/Operation.sol";

import {Consumption} from "./Allowance.sol";

enum Status {
    Ok,
    /// Or conition not met
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

struct Transaction {
    address to;
    uint256 value;
    Operation operation;
}

struct Context {
    address to;
    uint256 value;
    Operation operation;
    bytes32[] pluckedValues;
    uint256[] pluckedLocations;
}

struct Result {
    Status status;
    uint256 violatedNodeIndex;
    uint256 payloadLocation;
    Consumption[] consumptions;
}
