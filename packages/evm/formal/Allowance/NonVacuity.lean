import Allowance.Basic
import Allowance.Agree

/-!
# Non-vacuity of the allowance theorems

* A priced spend with different decimals goes through (`charge = .ok`), so
  the hypotheses of `scale_eq`, `charge_fits_iff`, `charge_covers`,
  `charge_pos` and `charged_covers` hold on a real conversion: 1.5 tokens
  with 6 decimals at price 2000 into an 18-decimal balance cost `3000e18`.
  One unit of a 6-decimal token at a price that makes it worth a third of
  a balance unit is charged 1 (rounded up once).
* `spending_limit` is tight: three transactions over two refill periods
  spend exactly the stored balance plus two refills, and a fourth one at
  the same time is refused.
* `update_limit`: transactions before and after an `accrueThenUpdate` go
  through, so its hypotheses hold with nonempty histories.

Checked with `rfl` / `decide` (no `native_decide`). The `update_limit`
example is tight too: 40 = 10 + 10 · 1 + 20 · 1.
-/

namespace Allowance.NonVacuity
open Allowance

theorem priced_ok :
    charge (.priced 1500000 (2000 * 10 ^ 18) 18 6) = .ok (3000 * 10 ^ 18) := by rfl

example : 3000 * 10 ^ 18 = ceilDiv (1500000 * (2000 * 10 ^ 18) * 10 ^ 18) (10 ^ 18 * 10 ^ 6) :=
  (charge_priced priced_ok).2

/-- Rounding up: a value of a third of a unit costs 1. -/
theorem dust_ok : charge (.priced 1 (10 ^ 18 / 3) 0 6) = .ok 1 := by rfl

example : worth 6 (.priced 1 (10 ^ 18 / 3) 0 6) ≤ 1 * 10 ^ (18 + 6) ∧
    1 * 10 ^ (18 + 6) < worth 6 (.priced 1 (10 ^ 18 / 3) 0 6) + 10 ^ (18 + 6) :=
  charge_covers (K := 6) (show (6 : Nat) ≤ 6 from Nat.le_refl _) dust_ok

example : 0 < 1 := charge_pos (by decide) dust_ok

example := charged_covers 6 [.priced 1500000 (2000 * 10 ^ 18) 18 6, .priced 1 (10 ^ 18 / 3) 0 6, .raw 5]
  (by
    intro sp hsp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsp
    rcases hsp with rfl | rfl | rfl
    · exact ⟨_, priced_ok⟩
    · exact ⟨_, dust_ok⟩
    · exact ⟨_, rfl⟩)
  (by
    intro sp hsp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hsp
    rcases hsp with rfl | rfl | rfl <;> simp [Fits])

/-! ## `spending_limit` is tight -/

/-- Refill 10 per 60 s, cap 100; stored balance 10 at time 0. -/
def c : Config := ⟨10, 100, 60⟩
def s0 : State := ⟨10, 0⟩

def txs : List (Nat × List Spend) :=
  [(0, [.raw 10]), (60, [.raw 4, .raw 6]), (130, [.raw 10]), (130, [.raw 1])]

/-- The first three go through, the fourth (over budget) is refused. -/
theorem run_txs : run c s0 txs = (⟨0, 120⟩, [.raw 10, .raw 4, .raw 6, .raw 10]) := by rfl

/-- Charged 30 = 10 + 10 · 2 periods: the bound of `spending_limit` is reached. -/
example : charged (run c s0 txs).2 = s0.balance + c.refill * periods c s0.timestamp 130 := by rfl

example : charged (run c s0 txs).2 ≤ s0.balance + c.refill * periods c s0.timestamp 130 :=
  spending_limit c s0 txs 130 (by decide)

/-! ## `update_limit` with nonempty histories -/

def c' : Config := ⟨20, 100, 30⟩

example :
    let a := accrueThenUpdate c (run c s0 [(0, [.raw 10])]).1 70
    charged (run c s0 [(0, [.raw 10])]).2 + charged (run c' a [(100, [.raw 30])]).2 ≤
      s0.balance + c.refill * periods c s0.timestamp 70 + c'.refill * periods c' 70 100 :=
  update_limit c c' s0 70 100 _ _ (by decide) (by decide)

/-- Both transactions went through: 10 before, 30 after (10 accrued under
    the old refill, plus one period of the new one). -/
example : charged (run c s0 [(0, [.raw 10])]).2 +
    charged (run c' (accrueThenUpdate c (run c s0 [(0, [.raw 10])]).1 70) [(100, [.raw 30])]).2 = 40 := by
  rfl

end Allowance.NonVacuity
