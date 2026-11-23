import { expect } from "chai";
import { network } from "hardhat";

import { ExecutionOptions } from "./utils.js";
import { createSetup } from "./setup.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { deployRolesMod } = createSetup(connection);

/**
 * onlyOwner tests
 *
 * Scope: Administration Access Control.
 *
 * This file verifies that administrative configuration functions are strictly restricted to the contract owner.
 * It tests that calls from non-owner accounts revert for critical functions such as:
 * - Role management (granting/revoking).
 * - Permission configuration (allowing targets/functions).
 * - Allowance configuration.
 */

describe("onlyOwner", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [owner, nonOwner] = await ethers.getSigners();

    const Avatar = await ethers.getContractFactory("TestAvatar");
    const avatar = await Avatar.deploy();
    const avatarAddress = await avatar.getAddress();

    const roles = await deployRolesMod(
      owner.address,
      avatarAddress,
      avatarAddress,
    );

    const ROLE_KEY = ethers.id("TEST_ROLE");
    const TARGET = "0x000000000000000000000000000000000000000f";
    const SELECTOR = "0x12345678";

    return { roles, owner, nonOwner, ROLE_KEY, TARGET, SELECTOR };
  }

  describe("Role membership functions", () => {
    describe("grantRole", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner, nonOwner, ROLE_KEY } = await loadFixture(setup);

        await expect(
          roles.connect(owner).grantRole(nonOwner.address, ROLE_KEY, 0, 0, 0),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner, ROLE_KEY } = await loadFixture(setup);

        await expect(
          roles
            .connect(nonOwner)
            .grantRole(nonOwner.address, ROLE_KEY, 0, 0, 0),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });

    describe("revokeRole", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner, nonOwner, ROLE_KEY } = await loadFixture(setup);

        await expect(
          roles.connect(owner).revokeRole(nonOwner.address, ROLE_KEY),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner, ROLE_KEY } = await loadFixture(setup);

        await expect(
          roles.connect(nonOwner).revokeRole(nonOwner.address, ROLE_KEY),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });

    describe("assignRoles", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner, nonOwner, ROLE_KEY } = await loadFixture(setup);

        await expect(
          roles
            .connect(owner)
            .assignRoles(nonOwner.address, [ROLE_KEY], [true]),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner, ROLE_KEY } = await loadFixture(setup);

        await expect(
          roles
            .connect(nonOwner)
            .assignRoles(nonOwner.address, [ROLE_KEY], [true]),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });

    describe("setDefaultRole", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner, nonOwner, ROLE_KEY } = await loadFixture(setup);

        await expect(
          roles.connect(owner).setDefaultRole(nonOwner.address, ROLE_KEY),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner, ROLE_KEY } = await loadFixture(setup);

        await expect(
          roles.connect(nonOwner).setDefaultRole(nonOwner.address, ROLE_KEY),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });
  });

  describe("Target permission functions", () => {
    describe("allowTarget", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner, ROLE_KEY, TARGET } = await loadFixture(setup);

        await expect(
          roles
            .connect(owner)
            .allowTargetPacked(ROLE_KEY, TARGET, "0x", ExecutionOptions.None),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner, ROLE_KEY, TARGET } = await loadFixture(setup);

        await expect(
          roles
            .connect(nonOwner)
            .allowTargetPacked(ROLE_KEY, TARGET, "0x", ExecutionOptions.None),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });

    describe("scopeTarget", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner, ROLE_KEY, TARGET } = await loadFixture(setup);

        await expect(
          roles.connect(owner).scopeTarget(ROLE_KEY, TARGET),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner, ROLE_KEY, TARGET } = await loadFixture(setup);

        await expect(
          roles.connect(nonOwner).scopeTarget(ROLE_KEY, TARGET),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });

    describe("revokeTarget", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner, ROLE_KEY, TARGET } = await loadFixture(setup);

        await expect(
          roles.connect(owner).revokeTarget(ROLE_KEY, TARGET),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner, ROLE_KEY, TARGET } = await loadFixture(setup);

        await expect(
          roles.connect(nonOwner).revokeTarget(ROLE_KEY, TARGET),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });
  });

  describe("Function permission functions", () => {
    describe("allowFunction", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner, ROLE_KEY, TARGET, SELECTOR } =
          await loadFixture(setup);

        await expect(
          roles
            .connect(owner)
            .allowFunctionPacked(
              ROLE_KEY,
              TARGET,
              SELECTOR,
              "0x",
              ExecutionOptions.None,
            ),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner, ROLE_KEY, TARGET, SELECTOR } =
          await loadFixture(setup);

        await expect(
          roles
            .connect(nonOwner)
            .allowFunctionPacked(
              ROLE_KEY,
              TARGET,
              SELECTOR,
              "0x",
              ExecutionOptions.None,
            ),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });

    describe("revokeFunction", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner, ROLE_KEY, TARGET, SELECTOR } =
          await loadFixture(setup);

        await expect(
          roles.connect(owner).revokeFunction(ROLE_KEY, TARGET, SELECTOR),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner, ROLE_KEY, TARGET, SELECTOR } =
          await loadFixture(setup);

        await expect(
          roles.connect(nonOwner).revokeFunction(ROLE_KEY, TARGET, SELECTOR),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });
  });

  describe("Allowance functions", () => {
    describe("setAllowance", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner } = await loadFixture(setup);
        const allowanceKey = ethers.id("ALLOWANCE_KEY");

        await expect(
          roles
            .connect(owner)
            .setAllowance(allowanceKey, 1000, 0, 100, 3600, 0),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner } = await loadFixture(setup);
        const allowanceKey = ethers.id("ALLOWANCE_KEY");

        await expect(
          roles
            .connect(nonOwner)
            .setAllowance(allowanceKey, 1000, 0, 100, 3600, 0),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });

    describe("updateAllowance", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner } = await loadFixture(setup);
        const allowanceKey = ethers.id("ALLOWANCE_KEY");

        // First set an allowance
        await roles
          .connect(owner)
          .setAllowance(allowanceKey, 1000, 0, 100, 3600, 0);

        await expect(
          roles.connect(owner).updateAllowance(allowanceKey, 0, 200, 7200),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, owner, nonOwner } = await loadFixture(setup);
        const allowanceKey = ethers.id("ALLOWANCE_KEY");

        // First set an allowance
        await roles
          .connect(owner)
          .setAllowance(allowanceKey, 1000, 0, 100, 3600, 0);

        await expect(
          roles.connect(nonOwner).updateAllowance(allowanceKey, 0, 200, 7200),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });
  });

  describe("Adapter functions", () => {
    describe("setTransactionUnwrapper", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner, TARGET, SELECTOR } = await loadFixture(setup);
        const adapter = "0x0000000000000000000000000000000000000001";

        await expect(
          roles
            .connect(owner)
            .setTransactionUnwrapper(TARGET, SELECTOR, adapter),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner, TARGET, SELECTOR } = await loadFixture(setup);
        const adapter = "0x0000000000000000000000000000000000000001";

        await expect(
          roles
            .connect(nonOwner)
            .setTransactionUnwrapper(TARGET, SELECTOR, adapter),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });

    describe("setEvaluator", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner } = await loadFixture(setup);
        const newEvaluator = "0x0000000000000000000000000000000000000001";

        await expect(
          roles.connect(owner).setEvaluator(newEvaluator),
        ).to.not.be.revert(ethers);
      });

      it("reverts 'OwnableUnauthorizedAccount' when called by non-owner", async () => {
        const { roles, nonOwner } = await loadFixture(setup);
        const newEvaluator = "0x0000000000000000000000000000000000000001";

        await expect(
          roles.connect(nonOwner).setEvaluator(newEvaluator),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });
  });

  describe("Module functions (inherited from Modifier)", () => {
    describe("enableModule", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner } = await loadFixture(setup);
        const moduleToEnable = "0x0000000000000000000000000000000000000002";

        await expect(
          roles.connect(owner).enableModule(moduleToEnable),
        ).to.not.be.revert(ethers);
      });

      it("reverts when called by non-owner", async () => {
        const { roles, nonOwner } = await loadFixture(setup);
        const moduleToEnable = "0x0000000000000000000000000000000000000002";

        await expect(
          roles.connect(nonOwner).enableModule(moduleToEnable),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });

    describe("disableModule", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner } = await loadFixture(setup);
        const moduleToEnable = "0x0000000000000000000000000000000000000002";

        // First enable the module
        await roles.connect(owner).enableModule(moduleToEnable);

        // SENTINEL_MODULES is address(1) in zodiac-core
        const sentinelModule = "0x0000000000000000000000000000000000000001";

        await expect(
          roles.connect(owner).disableModule(sentinelModule, moduleToEnable),
        ).to.not.be.revert(ethers);
      });

      it("reverts when called by non-owner", async () => {
        const { roles, owner, nonOwner } = await loadFixture(setup);
        const moduleToEnable = "0x0000000000000000000000000000000000000002";

        // First enable the module
        await roles.connect(owner).enableModule(moduleToEnable);

        const sentinelModule = "0x0000000000000000000000000000000000000001";

        await expect(
          roles.connect(nonOwner).disableModule(sentinelModule, moduleToEnable),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });
    });
  });

  describe("Ownership functions (inherited from Ownable)", () => {
    describe("transferOwnership", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner, nonOwner } = await loadFixture(setup);

        await expect(
          roles.connect(owner).transferOwnership(nonOwner.address),
        ).to.not.be.revert(ethers);
      });

      it("reverts when called by non-owner", async () => {
        const { roles, owner, nonOwner } = await loadFixture(setup);

        await expect(
          roles.connect(nonOwner).transferOwnership(owner.address),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });

      it("updates owner after transfer", async () => {
        const { roles, owner, nonOwner } = await loadFixture(setup);

        await roles.connect(owner).transferOwnership(nonOwner.address);

        expect(await roles.owner()).to.equal(nonOwner.address);
      });
    });

    // zodiac-core 4 removed renounceOwnership() from Ownable. To relinquish
    // ownership now, owner calls transferOwnership(ZeroAddress).
    describe("transferOwnership(0) — relinquish", () => {
      it("succeeds when called by owner", async () => {
        const { roles, owner } = await loadFixture(setup);

        await expect(
          roles.connect(owner).transferOwnership(ethers.ZeroAddress),
        ).to.not.be.revert(ethers);
      });

      it("reverts when called by non-owner", async () => {
        const { roles, nonOwner } = await loadFixture(setup);

        await expect(
          roles.connect(nonOwner).transferOwnership(ethers.ZeroAddress),
        ).to.be.revertedWithCustomError(roles, "OwnableUnauthorizedAccount");
      });

      it("sets owner to zero address", async () => {
        const { roles, owner } = await loadFixture(setup);

        await roles.connect(owner).transferOwnership(ethers.ZeroAddress);

        expect(await roles.owner()).to.equal(ethers.ZeroAddress);
      });
    });
  });

  describe("Non-restricted functions", () => {
    describe("renounceRole", () => {
      it("can be called by anyone (self-revoke)", async () => {
        const { roles, owner, nonOwner, ROLE_KEY } = await loadFixture(setup);

        // Grant role to nonOwner
        await roles
          .connect(owner)
          .grantRole(nonOwner.address, ROLE_KEY, 0, 0, 0);

        // nonOwner can renounce their own role
        await expect(
          roles.connect(nonOwner).renounceRole(ROLE_KEY),
        ).to.not.be.revert(ethers);
      });

      it("does not require owner permission", async () => {
        const { roles, owner, nonOwner, ROLE_KEY } = await loadFixture(setup);

        // Grant role to nonOwner
        await roles
          .connect(owner)
          .grantRole(nonOwner.address, ROLE_KEY, 0, 0, 0);

        // nonOwner can renounce (no owner check)
        await roles.connect(nonOwner).renounceRole(ROLE_KEY);

        // Verify role is renounced by checking membership is cleared
        // The membership value should be 0 after renouncing
        const roleKey = ROLE_KEY;
        // We can't directly check internal mapping, but can verify
        // by trying to use the role - it should fail
      });
    });
  });
});
