import Allowance.Basic

/-!
# Allowances: what a role can spend

**Charging** (`WithinAllowanceChecker._scaleInput`):
* `scale_eq`: scaling to the higher of the two precisions loses nothing:
  the charge is `⌈v·p·10^db / (10^18·10^di)⌉`, the value rounded up once.
* `charge_fits_iff`: a priced spend fits what is left, `R`, exactly when its
  value does: `v·p·10^db ≤ R·10^18·10^di` (no rounding in either direction
  at the limit).
* `charge_covers`, `charged_covers`: each charge is at least the value and
  less than one balance unit above it; summed over any spends, the total
  charged covers the total value (rounding never accumulates in the role's
  favour), and overcharges by less than one unit per spend.

**Accruing** (`AllowanceConsumer.accrue`):
* `accrue_eq`: closed form, `k` full periods credited at once.
* `accrue_accrue`: accruing at `t1` then `t2` is accruing at `t2`: when
  transactions happen does not change the balance.
* `accrue_cap`: refills never raise the balance above
  `max(balance, maxRefill)` (a balance already above the cap stays).
* `accrue_bounds`: with the storage word sizes nothing overflows.
* `update_retroactive`: `updateAllowance` keeps balance and timestamp
  without accruing, so the new refill also pays the periods that elapsed
  before the update.

**Spending limit** (`run`):
* `spending_limit`: over any transactions up to time `T`, the role is
  charged at most the starting balance plus `refill` per full period since
  the stored timestamp.
* `value_limit`: the same for the value of what it spends, in balance
  units, across any mix of prices and input decimals.
-/

namespace Allowance

/-! ## Ceiling division -/

theorem ceilDiv_spec {n d : Nat} (hd : 0 < d) :
    n ≤ ceilDiv n d * d ∧ ceilDiv n d * d < n + d := by
  unfold ceilDiv
  by_cases hn : n = 0
  · subst hn; simp; omega
  · rw [if_neg hn]
    have h1 := Nat.div_add_mod (n - 1) d
    have h2 := Nat.mod_lt (n - 1) hd
    rw [Nat.succ_mul, Nat.mul_comm]
    omega

theorem ceilDiv_unique {n d c : Nat} (hd : 0 < d) (h1 : n ≤ c * d) (h2 : c * d < n + d) :
    c = ceilDiv n d := by
  obtain ⟨e1, e2⟩ := ceilDiv_spec (n := n) hd
  have a : c < ceilDiv n d + 1 :=
    Nat.lt_of_mul_lt_mul_right (a := d) (by rw [Nat.succ_mul]; omega)
  have b : ceilDiv n d < c + 1 :=
    Nat.lt_of_mul_lt_mul_right (a := d) (by rw [Nat.succ_mul]; omega)
  omega

theorem ceilDiv_mul {n d m : Nat} (hd : 0 < d) (hm : 0 < m) :
    ceilDiv (n * m) (d * m) = ceilDiv n d := by
  obtain ⟨e1, e2⟩ := ceilDiv_spec (n := n) hd
  symm
  apply ceilDiv_unique (Nat.mul_pos hd hm)
  · rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right m e1
  · rw [← Nat.mul_assoc, ← Nat.add_mul]; exact Nat.mul_lt_mul_of_pos_right e2 hm

theorem ceilDiv_le_iff {n d R : Nat} (hd : 0 < d) : ceilDiv n d ≤ R ↔ n ≤ R * d := by
  obtain ⟨e1, e2⟩ := ceilDiv_spec (n := n) hd
  constructor
  · intro h; exact Nat.le_trans e1 (Nat.mul_le_mul_right d h)
  · intro h
    have : ceilDiv n d < R + 1 :=
      Nat.lt_of_mul_lt_mul_right (a := d) (by rw [Nat.succ_mul]; omega)
    omega

/-! ## Charging -/

theorem pow10_pos (e : Nat) : 0 < 10 ^ e := Nat.pow_pos (by decide)

theorem scale_core (v p db di : Nat) :
    ceilDiv (v * 10 ^ (max db di - di) * p) (10 ^ (max db di - db) * 10 ^ 18) =
      ceilDiv (v * p * 10 ^ db) (10 ^ 18 * 10 ^ di) := by
  by_cases hle : db ≤ di
  · rw [Nat.max_eq_right hle, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    have e : 10 ^ di = 10 ^ (di - db) * 10 ^ db := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hle]
    have h := ceilDiv_mul (n := v * p) (m := 10 ^ db)
      (Nat.mul_pos (pow10_pos (di - db)) (pow10_pos 18)) (pow10_pos db)
    rw [e, ← h]
    congr 1
    rw [Nat.mul_assoc (10 ^ (di - db)), Nat.mul_comm (10 ^ 18), ← Nat.mul_assoc, Nat.mul_comm (10 ^ (di - db) * 10 ^ db)]
  · have hlt : di ≤ db := by omega
    rw [Nat.max_eq_left hlt, Nat.sub_self, Nat.pow_zero, Nat.one_mul]
    have e : 10 ^ db = 10 ^ (db - di) * 10 ^ di := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hlt]
    have h := ceilDiv_mul (n := v * 10 ^ (db - di) * p) (m := 10 ^ di) (pow10_pos 18) (pow10_pos di)
    rw [e, ← h, ← Nat.mul_assoc, Nat.mul_right_comm v p]

theorem pow10?_some {e x : Nat} (h : pow10? e = some x) : x = 10 ^ e := by
  unfold pow10? at h; split at h <;> simp_all

theorem mul?_some {a b x : Nat} (h : mul? a b = some x) : x = a * b := by
  unfold mul? at h; split at h <;> simp_all

theorem scale_some {v p db di c : Nat} (h : scale v p db di = some c) :
    c = ceilDiv (v * 10 ^ (max db di - di) * p) (10 ^ (max db di - db) * 10 ^ 18) := by
  simp only [scale, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a, ha, n1, hn1, n, hn, b, hb, d, hd, rfl⟩ := h
  rw [pow10?_some ha] at hn1
  rw [mul?_some hn1] at hn
  rw [mul?_some hn, mul?_some hd, pow10?_some hb]

/-- **The charge is the value rounded up once**: scaling to `max db di`
    first is exact. -/
theorem scale_eq {v p db di c : Nat} (h : scale v p db di = some c) :
    c = ceilDiv (v * p * 10 ^ db) (10 ^ 18 * 10 ^ di) := by
  rw [scale_some h, scale_core]

theorem charge_priced {v p db di c : Nat} (h : charge (.priced v p db di) = .ok c) :
    0 < p ∧ c = ceilDiv (v * p * 10 ^ db) (10 ^ 18 * 10 ^ di) := by
  simp only [charge] at h
  split at h
  · contradiction
  · split at h
    · rename_i hs
      cases h; exact ⟨by omega, scale_eq hs⟩
    · contradiction

/-- **A priced spend fits what is left exactly when its value does.** -/
theorem charge_fits_iff {v p db di c R : Nat} (h : charge (.priced v p db di) = .ok c) :
    c ≤ R ↔ v * p * 10 ^ db ≤ R * (10 ^ 18 * 10 ^ di) := by
  obtain ⟨-, rfl⟩ := charge_priced h
  exact ceilDiv_le_iff (Nat.mul_pos (pow10_pos 18) (pow10_pos _))

/-- Input decimals at most `K`, so `worth K` is exact. -/
def Fits (K : Nat) : Spend → Prop
  | .raw _ => True
  | .priced _ _ _ di => di ≤ K

/-- **Each charge covers the value, and overcharges by less than one unit.** -/
theorem charge_covers {K c : Nat} {sp : Spend} (hK : Fits K sp) (h : charge sp = .ok c) :
    worth K sp ≤ c * 10 ^ (18 + K) ∧ c * 10 ^ (18 + K) < worth K sp + 10 ^ (18 + K) := by
  cases sp with
  | raw a =>
    simp only [charge, Except.ok.injEq] at h; subst h
    simp only [worth]; exact ⟨Nat.le_refl _, by have := pow10_pos (18 + K); omega⟩
  | priced v p db di =>
    simp only [Fits] at hK
    obtain ⟨-, rfl⟩ := charge_priced h
    have hU : 10 ^ (18 + K) = 10 ^ 18 * 10 ^ di * 10 ^ (K - di) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [hU, ← ceilDiv_mul (m := 10 ^ (K - di)) (Nat.mul_pos (pow10_pos 18) (pow10_pos _)) (pow10_pos _)]
    simp only [worth]
    exact ceilDiv_spec (Nat.mul_pos (Nat.mul_pos (pow10_pos 18) (pow10_pos _)) (pow10_pos _))

/-- A spend of a nonzero value is never free. -/
theorem charge_pos {v p db di c : Nat} (hv : 0 < v) (h : charge (.priced v p db di) = .ok c) :
    0 < c := by
  obtain ⟨hp, hc⟩ := charge_priced h
  have : 0 < v * p * 10 ^ db := Nat.mul_pos (Nat.mul_pos hv hp) (pow10_pos _)
  have h1 := (ceilDiv_spec (n := v * p * 10 ^ db) (Nat.mul_pos (pow10_pos 18) (pow10_pos di))).1
  rw [← hc] at h1
  apply Nat.pos_of_ne_zero; intro h0; rw [h0, Nat.zero_mul] at h1; omega

def AllOk (sps : List Spend) : Prop := ∀ sp ∈ sps, ∃ c, charge sp = .ok c

/-- **Summed over any spends, the total charged covers the total value**,
    and exceeds it by less than one balance unit per spend. -/
theorem charged_covers (K : Nat) :
    ∀ sps : List Spend, AllOk sps → (∀ sp ∈ sps, Fits K sp) →
      totalWorth K sps ≤ charged sps * 10 ^ (18 + K) ∧
      charged sps * 10 ^ (18 + K) + sps.length ≤ totalWorth K sps + sps.length * 10 ^ (18 + K)
  | [], _, _ => by simp [totalWorth, charged]
  | sp :: rest, hok, hfit => by
    obtain ⟨c, hc⟩ := hok sp (List.mem_cons_self ..)
    have ih := charged_covers K rest (fun x hx => hok x (List.mem_cons_of_mem _ hx))
      (fun x hx => hfit x (List.mem_cons_of_mem _ hx))
    have h1 := charge_covers (hfit sp (List.mem_cons_self ..)) hc
    have hco : chargeOf sp = c := by simp [chargeOf, hc]
    simp only [totalWorth, charged, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [hco, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega

/-! ## Accruing -/

/-- `k` periods of refill: unchanged at or above the cap, else capped. -/
def grow (c : Config) (b k : Nat) : Nat :=
  if c.maxRefill ≤ b then b
  else if b + c.refill * k < c.maxRefill then b + c.refill * k else c.maxRefill

theorem grow_zero (c : Config) (b : Nat) : grow c b 0 = b := by
  unfold grow; simp only [Nat.mul_zero, Nat.add_zero]
  split
  · rfl
  · split <;> omega

/-- **Closed form**: `k = (now - timestamp) / period` full periods are
    credited (`0` without a period, or when `now` is not after the
    timestamp), and the timestamp moves by `k` periods. -/
theorem accrue_eq (c : Config) (s : State) (now : Nat) :
    accrue c s now = ⟨grow c s.balance ((now - s.timestamp) / c.period),
      s.timestamp + (now - s.timestamp) / c.period * c.period⟩ := by
  cases s with
  | mk b ts =>
  unfold accrue
  simp only
  by_cases hp : c.period = 0
  · rw [if_pos hp, hp, Nat.div_zero, grow_zero]; simp
  rw [if_neg hp]
  by_cases hn : now ≤ ts
  · rw [if_pos hn, show now - ts = 0 by omega, Nat.zero_div, grow_zero]; simp
  rw [if_neg hn]
  generalize (now - ts) / c.period = k
  by_cases hk : k = 0
  · subst hk; rw [if_pos rfl, grow_zero]; simp
  rw [if_neg hk]
  unfold grow
  split <;> rfl

theorem grow_grow (c : Config) (b k1 k2 : Nat) :
    grow c (grow c b k1) k2 = grow c b (k1 + k2) := by
  unfold grow
  rw [Nat.mul_add]
  generalize c.refill * k1 = x
  generalize c.refill * k2 = y
  by_cases h1 : c.maxRefill ≤ b
  · simp [h1]
  · simp only [if_neg h1]
    by_cases h2 : b + x < c.maxRefill
    · rw [if_pos h2, if_neg (by omega), Nat.add_assoc]
    · rw [if_neg h2, if_pos (Nat.le_refl _), if_neg (by omega)]

/-- **Path independence**: accruing at `t1` and then at `t2` is accruing
    at `t2`. A transaction in between that spends nothing, or none at all,
    leaves the same balance. -/
theorem accrue_accrue (c : Config) (s : State) {t1 t2 : Nat} (h : t1 ≤ t2) :
    accrue c (accrue c s t1) t2 = accrue c s t2 := by
  rw [accrue_eq c s t1, accrue_eq, accrue_eq c s t2]
  simp only
  have hle : (t1 - s.timestamp) / c.period ≤ (t2 - s.timestamp) / c.period :=
    Nat.div_le_div_right (by omega)
  have hkP : (t1 - s.timestamp) / c.period * c.period ≤ t2 - s.timestamp :=
    Nat.le_trans (Nat.div_mul_le_self _ _) (by omega)
  generalize (t1 - s.timestamp) / c.period = k1 at hle hkP ⊢
  have e : (t2 - (s.timestamp + k1 * c.period)) / c.period =
      (t2 - s.timestamp) / c.period - k1 := by
    rw [Nat.sub_add_eq, Nat.mul_comm k1, Nat.sub_mul_div]
  rw [e, grow_grow, Nat.add_sub_of_le hle, Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_of_le hle]

theorem accrue_cap (c : Config) (s : State) (now : Nat) :
    (accrue c s now).balance ≤ max s.balance c.maxRefill := by
  rw [accrue_eq]; simp only [grow]
  split
  · omega
  · split <;> omega

theorem accrue_le (c : Config) (s : State) (now : Nat) :
    (accrue c s now).balance ≤ s.balance + c.refill * ((now - s.timestamp) / c.period) := by
  rw [accrue_eq]; simp only [grow]
  split
  · omega
  · split <;> omega

theorem accrue_time (c : Config) (s : State) (now : Nat) :
    s.timestamp ≤ (accrue c s now).timestamp ∧
      (accrue c s now).timestamp ≤ max s.timestamp now := by
  rw [accrue_eq]; simp only
  have := Nat.div_mul_le_self (now - s.timestamp) c.period
  constructor
  · omega
  · by_cases h : now ≤ s.timestamp
    · rw [show now - s.timestamp = 0 by omega, Nat.zero_div, Nat.zero_mul]; omega
    · omega

/-- **No overflow**: with the storage word sizes (`uint128` amounts,
    `uint64` times) the elapsed periods times the period fit `uint64`, the
    `uint256` sum `balance + refill * k` does not overflow, and the result
    fits the storage words again. -/
theorem accrue_bounds (c : Config) (s : State) (now : Nat)
    (hb : s.balance < 2 ^ 128) (hm : c.maxRefill < 2 ^ 128) (hr : c.refill < 2 ^ 128)
    (hts : s.timestamp < 2 ^ 64) (hnow : now < 2 ^ 64) :
    (now - s.timestamp) / c.period * c.period < 2 ^ 64 ∧
      s.balance + c.refill * ((now - s.timestamp) / c.period) < 2 ^ 256 ∧
      (accrue c s now).timestamp < 2 ^ 64 ∧ (accrue c s now).balance < 2 ^ 128 := by
  have h1 := Nat.div_mul_le_self (now - s.timestamp) c.period
  have h2 : (now - s.timestamp) / c.period ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.div_le_self _ _) (by omega)
  have h3 : c.refill * ((now - s.timestamp) / c.period) ≤ c.refill * 2 ^ 64 :=
    Nat.mul_le_mul_left _ h2
  have h4 : c.refill * 2 ^ 64 < 2 ^ 128 * 2 ^ 64 :=
    Nat.mul_lt_mul_of_pos_right hr (Nat.pow_pos (by decide))
  have h5 : (2 : Nat) ^ 128 * 2 ^ 64 + 2 ^ 128 ≤ 2 ^ 256 := by
    rw [← Nat.pow_add]
    have : (2 : Nat) ^ 128 ≤ 2 ^ 192 := Nat.pow_le_pow_right (by decide) (by decide)
    have : (2 : Nat) ^ 192 + 2 ^ 192 ≤ 2 ^ 256 := by
      rw [← Nat.two_mul, ← Nat.pow_succ']; exact Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have hc := accrue_cap c s now
  have ht := accrue_time c s now
  refine ⟨by omega, by omega, ?_, by omega⟩
  omega

/-! ## Spending limit -/

theorem consumeAll_ok (bal : Nat) :
    ∀ (sps : List Spend) (u used : Nat), u ≤ bal → consumeAll bal u sps = .ok used →
      used = u + charged sps ∧ used ≤ bal ∧ AllOk sps
  | [], u, used, hu, h => by
    simp only [consumeAll, Except.ok.injEq] at h
    subst h; simp [charged, AllOk]; exact hu
  | sp :: rest, u, used, hu, h => by
    simp only [consumeAll] at h
    split at h
    · contradiction
    · rename_i a ha
      split at h
      · contradiction
      · obtain ⟨e, hle, hok⟩ := consumeAll_ok bal rest (u + a) used (by omega) h
        have hco : chargeOf sp = a := by simp [chargeOf, ha]
        refine ⟨?_, hle, ?_⟩
        · simp only [charged, List.map_cons, List.sum_cons, hco] at e ⊢
          omega
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨a, ha⟩
          · exact hok x hx

/-- The invariant of `spending_limit`: what is left plus what was charged
    stays within the starting balance plus the refill of the periods the
    stored timestamp has moved past `t0`. -/
def Inv (c : Config) (t0 b0 T : Nat) (s : State) (U : Nat) : Prop :=
  t0 ≤ s.timestamp ∧ s.timestamp ≤ max t0 T ∧
    s.balance + U ≤ b0 + c.refill * periods c t0 s.timestamp

theorem periods_accrue (c : Config) (s : State) (now t0 : Nat) (h : t0 ≤ s.timestamp) :
    periods c t0 (accrue c s now).timestamp =
      periods c t0 s.timestamp + (now - s.timestamp) / c.period := by
  rw [accrue_eq]; unfold periods
  split
  · rename_i hp; rw [hp, Nat.div_zero]
  · rename_i hp
    rw [show s.timestamp + (now - s.timestamp) / c.period * c.period - t0 =
        (s.timestamp - t0) + (now - s.timestamp) / c.period * c.period by omega,
      Nat.add_mul_div_right _ _ (by omega)]

theorem tx_inv (c : Config) (t0 b0 T : Nat) (s s' : State) (U now : Nat) (sps : List Spend)
    (hnow : now ≤ T) (hI : Inv c t0 b0 T s U) (h : tx c s now sps = .ok s') :
    Inv c t0 b0 T s' (U + charged sps) ∧ AllOk sps := by
  unfold tx at h
  split at h
  · rename_i he; subst he
    simp only [Except.ok.injEq] at h; subst h
    simp only [charged, List.map_nil, List.sum_nil, Nat.add_zero]
    exact ⟨hI, fun _ hx => by simp at hx⟩
  · dsimp only at h
    split at h
    · rename_i used hc
      simp only [Except.ok.injEq] at h; subst h
      obtain ⟨e, hle, hok⟩ := consumeAll_ok _ sps 0 used (Nat.zero_le _) hc
      obtain ⟨i1, i2, i3⟩ := hI
      have ha := accrue_le c s now
      have hp := periods_accrue c s now t0 i1
      have ht := accrue_time c s now
      refine ⟨⟨by simp only; omega, by simp only; omega, ?_⟩, hok⟩
      simp only
      rw [hp, Nat.mul_add]
      omega
    · contradiction

theorem run_inv (c : Config) (t0 b0 T : Nat) :
    ∀ (txs : List (Nat × List Spend)) (s : State) (U : Nat),
      (∀ x ∈ txs, x.1 ≤ T) → Inv c t0 b0 T s U →
        Inv c t0 b0 T (run c s txs).1 (U + charged (run c s txs).2) ∧ AllOk (run c s txs).2
  | [], s, U, _, hI => by
    simp only [run, charged, List.map_nil, List.sum_nil, Nat.add_zero]
    exact ⟨hI, fun _ hx => by simp at hx⟩
  | (now, sps) :: rest, s, U, hT, hI => by
    have hT' : ∀ x ∈ rest, x.1 ≤ T := fun x hx => hT x (List.mem_cons_of_mem _ hx)
    simp only [run]
    split
    · rename_i s' h
      obtain ⟨hI', hok⟩ := tx_inv c t0 b0 T s s' U now sps (hT _ (List.mem_cons_self ..)) hI h
      obtain ⟨ih, hok'⟩ := run_inv c t0 b0 T rest s' (U + charged sps) hT' hI'
      simp only [charged, List.map_append, List.sum_append] at ih ⊢
      refine ⟨by rw [← Nat.add_assoc]; exact ih, ?_⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hok x hx
      · exact hok' x hx
    · exact run_inv c t0 b0 T rest s U hT' hI

theorem periods_mono (c : Config) {t0 t T : Nat} (h : t ≤ max t0 T) :
    periods c t0 t ≤ periods c t0 T := by
  unfold periods; split
  · exact Nat.le_refl _
  · exact Nat.div_le_div_right (by omega)

/-- **Spending limit**: over any transactions at times up to `T`, the role
    is charged at most the stored balance plus `refill` for each full
    period from the stored timestamp to `T`. -/
theorem spending_limit (c : Config) (s0 : State) (txs : List (Nat × List Spend)) (T : Nat)
    (hT : ∀ x ∈ txs, x.1 ≤ T) :
    charged (run c s0 txs).2 ≤ s0.balance + c.refill * periods c s0.timestamp T := by
  have hI : Inv c s0.timestamp s0.balance T s0 0 :=
    ⟨Nat.le_refl _, by omega, by simp [periods]⟩
  obtain ⟨⟨_, h2, h3⟩, _⟩ := run_inv c s0.timestamp s0.balance T txs s0 0 hT hI
  have := Nat.mul_le_mul_left c.refill (periods_mono c h2)
  omega

theorem run_sub (c : Config) (P : Spend → Prop) :
    ∀ (txs : List (Nat × List Spend)) (s : State), (∀ x ∈ txs, ∀ sp ∈ x.2, P sp) →
      ∀ sp ∈ (run c s txs).2, P sp
  | [], s, _ => by simp [run]
  | (now, sps) :: rest, s, h => by
    have h' : ∀ x ∈ rest, ∀ sp ∈ x.2, P sp := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [run]
    split
    · rename_i s' _
      intro sp hsp
      rcases List.mem_append.mp hsp with hx | hx
      · exact h _ (List.mem_cons_self ..) sp hx
      · exact run_sub c P rest s' h' sp hx
    · exact run_sub c P rest s h'

/-- **Value limit**: the value of everything spent, in balance units
    (times `10^(18+K)`, for input decimals up to `K`), across any mix of
    prices and decimals, is at most the spending limit. Rounding never adds
    up in the role's favour. -/
theorem value_limit (c : Config) (s0 : State) (txs : List (Nat × List Spend)) (T K : Nat)
    (hT : ∀ x ∈ txs, x.1 ≤ T) (hK : ∀ x ∈ txs, ∀ sp ∈ x.2, Fits K sp) :
    totalWorth K (run c s0 txs).2 ≤
      (s0.balance + c.refill * periods c s0.timestamp T) * 10 ^ (18 + K) := by
  have hI : Inv c s0.timestamp s0.balance T s0 0 :=
    ⟨Nat.le_refl _, by omega, by simp [periods]⟩
  have hok := (run_inv c s0.timestamp s0.balance T txs s0 0 hT hI).2
  have h1 := (charged_covers K _ hok (run_sub c (Fits K) txs s0 hK)).1
  exact Nat.le_trans h1 (Nat.mul_le_mul_right _ (spending_limit c s0 txs T hT))

/-- **`updateAllowance` is retroactive**: it keeps balance and timestamp
    without accruing, so a new refill also pays for the periods since the
    last accrual. Here, an allowance with no refill, untouched for ten
    periods, credits ten periods of the new refill at once. -/
theorem update_retroactive :
    let old : Config := ⟨0, 2 ^ 128 - 1, 100⟩
    let new : Config := ⟨5, 2 ^ 128 - 1, 100⟩
    let s : State := ⟨0, 0⟩
    -- accrued before the update: nothing; after: 10 periods of the new refill
    (accrue old s 1000).balance = 0 ∧ (accrue new s 1000).balance = 50 ∧
      (accrue new (accrue old s 1000) 1000).balance = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-! ## Changing the refill: `accrueThenUpdate` -/

/-- The update keeps the balance accrued under the old configuration and
    starts the new one no earlier than `now`. -/
theorem accrueThenUpdate_spec (c : Config) (s : State) (now : Nat) :
    (accrueThenUpdate c s now).balance = (accrue c s now).balance ∧
      now ≤ (accrueThenUpdate c s now).timestamp :=
  ⟨rfl, Nat.le_max_left _ _⟩

/-- **No retroactive refill.** Transactions under the old configuration `c`
    up to `now`, the update at `now`, then transactions under the new
    configuration `c'` up to `T`: the role is charged at most the starting
    balance, plus the old refill for the periods up to `now`, plus the new
    refill for the periods after the update. -/
theorem update_limit (c c' : Config) (s0 : State) (now T : Nat)
    (before after : List (Nat × List Spend))
    (hb : ∀ x ∈ before, x.1 ≤ now) (ha : ∀ x ∈ after, x.1 ≤ T) :
    let a := accrueThenUpdate c (run c s0 before).1 now
    charged (run c s0 before).2 + charged (run c' a after).2 ≤
      s0.balance + c.refill * periods c s0.timestamp now +
        c'.refill * periods c' now T := by
  intro a
  simp only [a, accrueThenUpdate]
  have hI : Inv c s0.timestamp s0.balance now s0 0 :=
    ⟨Nat.le_refl _, by omega, by simp [periods]⟩
  obtain ⟨⟨i1, i2, i3⟩, _⟩ := run_inv c s0.timestamp s0.balance now before s0 0 hb hI
  generalize (run c s0 before).1 = f at i1 i2 i3 ⊢
  generalize charged (run c s0 before).2 = U1 at i3 ⊢
  have hp := periods_accrue c f now s0.timestamp i1
  have hl := accrue_le c f now
  have ht := accrue_time c f now
  have hm := Nat.mul_le_mul_left c.refill
    (periods_mono c (t0 := s0.timestamp) (T := now) (t := (accrue c f now).timestamp) (by omega))
  have h2 := spending_limit c' ⟨(accrue c f now).balance, max now (accrue c f now).timestamp⟩
    after T ha
  have hn : periods c' (max now (accrue c f now).timestamp) T ≤ periods c' now T := by
    unfold periods; split
    · exact Nat.le_refl _
    · exact Nat.div_le_div_right (by omega)
  have hn' := Nat.mul_le_mul_left c'.refill hn
  simp only at h2
  rw [hp, Nat.mul_add] at hm
  omega

/-- Contrast: the contract's `updateAllowance` keeps the stored state, and
    the new refill pays for periods before the update
    (`update_retroactive`); `accrueThenUpdate` credits those periods at
    the old refill, here nothing. -/
theorem accrueThenUpdate_not_retroactive :
    let old : Config := ⟨0, 2 ^ 128 - 1, 100⟩
    let new : Config := ⟨5, 2 ^ 128 - 1, 100⟩
    (accrue new (accrueThenUpdate old ⟨0, 0⟩ 1000) 1000).balance = 0 ∧
      (accrue new (accrueThenUpdate old ⟨0, 0⟩ 1000) 1100).balance = 5 := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- A shorter period does not pay for the partly elapsed old one: old period
    100 last accrued at 1000, update at 1099 to period 1. Keeping the
    accrued timestamp (1000) would credit 99 new periods at once. -/
theorem accrueThenUpdate_shorter_period :
    let old : Config := ⟨1, 2 ^ 128 - 1, 100⟩
    let new : Config := ⟨1, 2 ^ 128 - 1, 1⟩
    (accrue new (accrueThenUpdate old ⟨0, 1000⟩ 1099) 1099).balance = 0 ∧
      (accrue new (accrue old ⟨0, 1000⟩ 1099) 1099).balance = 99 := by
  refine ⟨?_, ?_⟩ <;> rfl

end Allowance
