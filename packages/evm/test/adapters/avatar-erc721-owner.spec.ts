import { after, describe, it } from "node:test";
import { network } from "hardhat";
import { encodeFunctionData, toFunctionSelector } from "viem";
import type { Hex } from "viem";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";

import {
  Encoding,
  ExecutionOptions,
  Operator,
  ConditionViolationStatus,
  packConditions,
} from "../utils.js";
import { createSetup } from "../setup.js";

const AddressOne = "0x0000000000000000000000000000000000000001";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { deployRolesMod } = createSetup(connection);

describe("AvatarIsOwnerOfERC721", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const ROLE_KEY =
      "0x0000000000000000000000000000000000000000000000000000000000000001" as const;

    const [owner, invoker] = await viem.getWalletClients();

    const avatar = await viem.deployContract("TestAvatar");
    const avatarAddress = avatar.address;

    const roles = await deployRolesMod(
      owner.account.address,
      avatarAddress,
      avatarAddress,
    );

    await roles.write.grantRole(
      [invoker.account.address, ROLE_KEY, 0n, 0n, 0n],
      { account: owner.account },
    );
    await roles.write.setDefaultRole([invoker.account.address, ROLE_KEY], {
      account: owner.account,
    });

    const mockERC721 = await viem.deployContract("MockERC721");
    const mockERC721Address = mockERC721.address;
    const SELECTOR = toFunctionSelector("doSomething(uint256,uint256)");

    await roles.write.scopeTarget([ROLE_KEY, mockERC721Address], {
      account: owner.account,
    });

    const customChecker = await viem.deployContract("AvatarIsOwnerOfERC721");
    const customCheckerAddress = customChecker.address;

    // Extra bytes (padding) for the custom checker address in compValue
    const extra = "000000000000000000000000";

    const packed = await packConditions(roles, [
      {
        parent: 0,
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        compValue: "0x",
      },
      {
        parent: 0,
        paramType: Encoding.Static,
        operator: Operator.Custom,
        compValue: `${customCheckerAddress}${extra}` as Hex,
      },
      {
        parent: 0,
        paramType: Encoding.Static,
        operator: Operator.Pass,
        compValue: "0x",
      },
    ]);
    await roles.write.allowFunctionPacked(
      [ROLE_KEY, mockERC721Address, SELECTOR, packed, ExecutionOptions.None],
      { account: owner.account },
    );

    async function invoke(tokenId: bigint, someParam: bigint) {
      return roles.write.execTransactionFromModule(
        [
          mockERC721Address,
          0n,
          encodeFunctionData({
            abi: mockERC721.abi,
            functionName: "doSomething",
            args: [tokenId, someParam],
          }),
          0,
        ],
        { account: invoker.account },
      );
    }

    return {
      roles,
      avatar,
      mockERC721,
      invoke,
    };
  }

  it("passes when avatar owns the token", async () => {
    const { avatar, mockERC721, invoke } = await loadFixture(setup);
    const avatarAddress = avatar.address;

    const tokenId = 6789n;
    const someParam = 123n;

    await mockERC721.write.mint([avatarAddress, tokenId]);

    await invoke(tokenId, someParam);
  });

  it("fails when avatar does not own the token", async () => {
    const { roles, mockERC721, invoke } = await loadFixture(setup);

    const tokenId = 12345n;
    const someParam = 123n;

    await mockERC721.write.mint([AddressOne, tokenId]);

    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(tokenId, someParam),
      roles,
      "ConditionViolation",
      [
        ConditionViolationStatus.CustomConditionViolation,
        1n, // Custom node
        anyValue,
      ],
    );
  });
});
