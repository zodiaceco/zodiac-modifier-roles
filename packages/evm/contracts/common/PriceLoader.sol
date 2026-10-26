// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../periphery/interfaces/IPricing.sol";
import "../types/Types.sol";

/**
 * @title PriceLoader
 * @notice Library for retrieving exchange rates from IPricing adapters.
 *
 * @dev The adapter returns a price with 18 decimals precision. Applying that
 *      price and any decimal scaling is handled by the caller.
 *
 * @author gnosisguild
 */
library PriceLoader {
    uint256 private constant PRICE_DECIMALS = 18;
    uint256 private constant ONE = 10 ** PRICE_DECIMALS;

    /**
     * @dev Safely invokes pricing adapter via staticcall.
     *
     *  Price Adapter (IPricing.getPrice) Error Scenarios:
     *  | Scenario              | staticcall Result     | Behavior                      | Status                          |
     *  |-----------------------|-----------------------|-------------------------------|---------------------------------|
     *  | No code at address    | (true, "")            | extcodesize == 0              | PricingAdapterNotAContract      |
     *  | Wrong interface       | (false, "")           | staticcall fails              | PricingAdapterReverted          |
     *  | Function reverts      | (false, <error data>) | staticcall fails              | PricingAdapterReverted          |
     *  | Returns wrong type    | (true, <len != 32>)   | returnData.length != 32       | PricingAdapterInvalidResult     |
     *  | Returns zero price    | (true, <32 bytes>)    | price == 0                    | PricingAdapterZeroPrice         |
     *
     */

    function load(
        address adapter,
        bytes memory params
    ) internal view returns (Status, uint256) {
        if (adapter == address(0)) {
            return (Status.Ok, ONE);
        }

        uint256 size;
        assembly {
            size := extcodesize(adapter)
        }
        if (size == 0) {
            return (Status.PricingAdapterNotAContract, 0);
        }

        (bool success, bytes memory returnData) = adapter.staticcall(
            abi.encodeCall(IPricing.getPrice, (params))
        );

        if (!success) {
            return (Status.PricingAdapterReverted, 0);
        }

        if (returnData.length != 32) {
            return (Status.PricingAdapterInvalidResult, 0);
        }

        uint256 price = uint256(bytes32(returnData));
        if (price == 0) {
            return (Status.PricingAdapterZeroPrice, 0);
        }

        return (Status.Ok, price);
    }
}
