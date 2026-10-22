// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

/**
 * @notice Represents an allowance with periodic refilling capability.
 *
 * @dev The struct layout is storage-optimized: fields updated together during
 * accrual (`balance` and `timestamp`) share word2, minimizing SSTORE
 *
 * Storage Layout (2 words, 64 bytes, 512 bits):
 * ┌────────────────────────────────┬────────────────────────────────┐
 * │           maxRefill            │             refill             │
 * │            128 bits            │            128 bits            │
 * ├────────────────┬───────────────┴───────────────┬────────────────┤
 * │   timestamp    │            balance            │     period     │
 * │    64 bits     │           128 bits            │    64 bits     │
 * └────────────────┴───────────────────────────────┴────────────────┘
 *
 * @custom:member refill Amount added to balance each period.
 * @custom:member maxRefill Cap at which refilling stops.
 * @custom:member period Refill interval in seconds. Zero means one-time use.
 * @custom:member balance Current available allowance.
 * @custom:member timestamp Last refill time.
 */
struct Allowance {
    uint128 refill;
    uint128 maxRefill;
    uint64 period;
    uint128 balance;
    uint64 timestamp;
}

struct Consumption {
    bytes32 allowanceKey;
    uint128 balance;
    uint128 consumed;
    uint64 timestamp;
}
