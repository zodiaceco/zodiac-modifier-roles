/**
 * Runs the cases of packages/evm/specs/integrity.cases.ts against
 * `checkStored`.
 *
 * `checkStored` gives no reason for a rejection, so only the verdict is
 * compared: a valid case is accepted, an invalid one is rejected.
 */
import { describe, expect, it } from "vitest"

import { integrityCases } from "../../../../evm/specs/integrity.cases"
import { checkStoredConditions } from "./checkStored"

describe("integrity cases", () => {
  for (const { rule, name, flat, valid } of integrityCases) {
    it(`${rule} ${valid ? "accepts" : "rejects"} ${name}`, () => {
      expect(checkStoredConditions(flat) !== undefined).toBe(valid)
    })
  }
})
