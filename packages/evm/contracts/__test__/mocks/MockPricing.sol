// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

contract MockPricing {
    uint256 private immutable _price;

    constructor(uint256 price) {
        _price = price;
    }

    function getPrice(bytes calldata) external view returns (uint256) {
        return _price;
    }
}

/// @dev Mock that requires specific params, reverts otherwise
contract MockPricingParameterized {
    mapping(bytes32 => uint256) private _prices;
    mapping(bytes32 => bool) private _set;

    function setPrice(bytes calldata params, uint256 price) external {
        _prices[keccak256(params)] = price;
        _set[keccak256(params)] = true;
    }

    function getPrice(bytes calldata params) external view returns (uint256) {
        bytes32 key = keccak256(params);
        require(_set[key], "MockPricingParameterized: unknown params");
        return _prices[key];
    }
}

/// @dev Mock that requires empty params, reverts otherwise
contract MockPricingEmptyParams {
    uint256 private immutable _price;

    constructor(uint256 price) {
        _price = price;
    }

    function getPrice(bytes calldata params) external view returns (uint256) {
        require(
            params.length == 0,
            "MockPricingEmptyParams: expected empty params"
        );
        return _price;
    }
}

/// @dev Contract with code but no getPrice() and no fallback
contract MockPricingNoInterface {
    function dummy() external pure returns (uint256) {
        return 42;
    }
}

/// @dev Contract that implements IPricing but always reverts
contract MockPricingReverting {
    function getPrice(bytes calldata) external pure returns (uint256) {
        revert("MockPricing: intentional revert");
    }
}

/// @dev Contract with matching selector but wrong return type
contract MockPricingWrongReturn {
    function getPrice(bytes calldata) external pure returns (uint256, uint256) {
        return (123, 456);
    }
}
