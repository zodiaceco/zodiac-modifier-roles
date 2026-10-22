// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "./interfaces/ICustomCondition.sol";

/**
 * @title   AvatarIsOwnerOfERC721
 * @notice  Custom condition that validates if the avatar owns a specific ERC721
 *          token.
 *
 * @author  gnosisguild
 */
interface IModifier {
    function avatar() external view returns (address);

    function target() external view returns (address);
}

interface IERC721 {
    function ownerOf(uint256 tokenId) external view returns (address);
}

contract AvatarIsOwnerOfERC721 is ICustomCondition {
    function check(
        address to,
        uint256 /* value */,
        bytes calldata data,
        Operation /* operation */,
        uint256 location,
        uint256 size,
        bytes calldata /* extra */,
        bytes32[] calldata /* pluckedValues */
    )
        public
        view
        returns (bool success, AllowanceConsumption[] memory consumptions)
    {
        address avatar = IModifier(msg.sender).avatar();
        uint256 tokenId = uint256(bytes32(data[location:location + size]));
        success = IERC721(to).ownerOf(tokenId) == avatar;
        consumptions = new AllowanceConsumption[](0);
    }
}
