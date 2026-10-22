// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

/**
 * @notice Interface for pricing contracts
 * @dev Returns a price with 18 decimals precision
 */
interface IPricing {
    function getPrice(
        bytes calldata params
    ) external view returns (uint256 price);
}
