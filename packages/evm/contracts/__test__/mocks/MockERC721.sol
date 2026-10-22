// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity ^0.8.0;

contract MockERC721 {
    mapping(uint256 tokenId => address owner) public ownerOf;

    function mint(address to, uint256 tokenId) external {
        ownerOf[tokenId] = to;
    }

    function doSomething(uint256 tokenId, uint256 someParam) external {}
}
