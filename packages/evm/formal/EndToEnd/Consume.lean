import Evaluate.Model
import Allowance.Basic

/-!
# What an evaluation charges, and what `_persist` stores

`Allowance` proves the spending limit for transactions that each make a
list of spends. This file connects it to the evaluator and to settlement:

* `evalC_steps`: when `evaluate` passes, its consumption list is the input
  list after a sequence of successful `consume` steps (the charges on the
  path that passed). Failed branches leave no trace.
* `steps_spec`: along such steps the list keeps one entry per key, with the
  accrued balance, and for each key the steps are exactly
  `Allowance.consumeAll` on that key's charges.
* `persist_get`: with one entry per key, `_persist` (which writes every
  entry, in order) stores each key's entry once. A second entry for a key
  would overwrite the first; the list never has one.
* `persist_tx`: so, for every key, what `_persist` stores after the
  evaluations is `Allowance.tx` on that key's charges.
-/

namespace EndToEnd
open DecoderFaithfulness DecoderFaithfulness.Roles Evaluate

/-! ## Steps -/

/-- Successful `consume` steps, with accrued balances `bal`, and the charges
    `(key, amount)` they make. -/
inductive Steps (bal : Bytes → Nat) : List Consumption → List (Bytes × Nat) → List Consumption → Prop
  | nil (c : List Consumption) : Steps bal c [] c
  | step {c c' c'' : List Consumption} {k : Bytes} {a : Nat} {log : List (Bytes × Nat)}
      (env : Env) (hb : env.balance = bal) (h : consume env c k a = (sOk, c'))
      (rest : Steps bal c' log c'') : Steps bal c ((k, a) :: log) c''

theorem Steps.trans {bal : Bytes → Nat} {c c' c'' : List Consumption} {l1 l2 : List (Bytes × Nat)}
    (h1 : Steps bal c l1 c') (h2 : Steps bal c' l2 c'') : Steps bal c (l1 ++ l2) c'' := by
  induction h1 with
  | nil => exact h2
  | step env hb h _ ih => exact .step env hb h (ih h2)

/-- The evaluation passed with consumptions reached from `cons` by steps. -/
def StepsOk (env : Env) (cons : List Consumption) (r : Res) : Prop :=
  r.status = sOk → ∃ log, Steps env.balance cons log r.cons

theorem ok_steps (env : Env) (cons : List Consumption) (sl : Slots) :
    StepsOk env cons (Evaluate.ok cons sl) := fun _ => ⟨[], .nil cons⟩

theorem violation_steps (env : Env) (cons : List Consumption) {s : Nat} (sl : Slots) (hs : s ≠ sOk) :
    StepsOk env cons (violation s sl) := fun h => absurd h hs

theorem result_steps (env : Env) {cons cons' : List Consumption} (s : Nat) (sl : Slots)
    (h : s = sOk → ∃ log, Steps env.balance cons log cons') : StepsOk env cons (result s cons' sl) := by
  unfold result
  split
  · rename_i hs; exact fun _ => h hs
  · rename_i hs; exact violation_steps env cons sl hs

theorem consume_steps (env : Env) (cons : List Consumption) (k : Bytes) (a : Nat)
    (h : (consume env cons k a).1 = sOk) :
    Steps env.balance cons [(k, a)] (consume env cons k a).2 :=
  .step env rfl (by rw [← h]) (.nil _)

theorem applyCharges_steps (env : Env) :
    ∀ (chs : List (Bytes × Nat)) (cons : List Consumption), (applyCharges env cons chs).1 = sOk →
      ∃ log, Steps env.balance cons log (applyCharges env cons chs).2
  | [], cons, _ => ⟨[], by simp only [applyCharges]; exact .nil cons⟩
  | (k, a) :: rest, cons, h => by
    unfold applyCharges at h ⊢
    simp only at h ⊢
    split at h
    · rename_i hne; exact absurd h hne
    · rename_i hok
      rw [if_neg hok]
      have hok' : (consume env cons k a).1 = sOk := by simpa using hok
      obtain ⟨log, hl⟩ := applyCharges_steps env rest _ h
      exact ⟨_, (consume_steps env cons k a hok').trans hl⟩

theorem allowance_steps (env : Env) (cons : List Consumption) (amount : Nat) (cv : Bytes)
    (h : (allowance env cons amount cv).1 = sOk) :
    ∃ log, Steps env.balance cons log (allowance env cons amount cv).2 := by
  unfold allowance at h ⊢
  by_cases hl : cv.length = 32
  · simp only [hl, ite_true, ne_eq, not_true_eq_false, ite_false] at h ⊢
    exact ⟨_, consume_steps env cons _ _ h⟩
  · simp only [hl, ite_false] at h ⊢
    by_cases hs : (env.scale cv amount).1 = sOk
    · simp only [hs, ne_eq, not_true_eq_false, ite_false] at h ⊢
      exact ⟨_, consume_steps env cons _ _ h⟩
    · simp [hs] at h

theorem leadingCheck_ne_ok {data : Calldata} {loc : Nat} {cv : Bytes} {s : Nat}
    (h : leadingCheck data loc cv = some s) : s ≠ sOk := by
  unfold leadingCheck at h
  repeat' split at h
  all_goals (simp at h; try (subst h; decide))

theorem childrenE_ne_ok {data : Calldata} {loc : Nat} {c : Condition} {s : Nat}
    (h : childrenE data loc c = .inl s) : s ≠ sOk := by
  unfold childrenE at h; split at h
  · simp at h; rw [← h]; decide
  · simp at h

theorem zipLocsGo_ne_ok (data : Calldata) (n : Nat) (cv : Bytes) :
    ∀ (fields : List Condition) (sl : Slots) (f : Nat) (len : Option Nat) (acc : List (List Nat))
      (s : Nat), zipLocsGo data n cv fields sl f len acc = .inl s → s ≠ sOk
  | [], _, _, _, _, _, h => by simp [zipLocsGo] at h
  | fd :: rest, sl, f, len, acc, s, h => by
    unfold zipLocsGo at h
    split at h
    · simp at h; rw [← h]; decide
    · split at h
      · simp at h; rw [← h]; decide
      · split at h
        · exact childrenE_ne_ok (by rename_i heq; simp at h; rw [← h]; exact heq)
        · simp at h; rw [← h]; decide
        · split at h
          · split at h
            · simp at h; rw [← h]; decide
            · exact zipLocsGo_ne_ok data n cv rest sl _ _ _ s h
          · exact zipLocsGo_ne_ok data n cv rest sl _ _ _ s h

theorem zipLocs_ne_ok {data : Calldata} {n : Nat} {cv : Bytes} {fields : List Condition}
    {sl : Slots} {s : Nat} (h : zipLocs data n cv fields sl = .inl s) : s ≠ sOk :=
  zipLocsGo_ne_ok data n cv fields sl 0 none [] s h

/-! ## The evaluator passes by steps -/

section
variable (env : Env) (data : Calldata) (n : Nat)
  (hcustom : ∀ cv l sz vals s, env.customCall cv l sz vals = .inl s → s ≠ sOk)

/-- The induction hypothesis: every evaluation at `fuel`. -/
def EvalSteps (fuel : Nat) : Prop :=
  ∀ loc c cons sl, StepsOk env cons (evalC env data n fuel loc c cons sl)

theorem seqLoop_steps {f : Nat} (IH : EvalSteps env data n f) :
    ∀ (xs : List (Condition × Nat)) (cons : List Consumption) (sl : Slots),
      StepsOk env cons (seqLoop env data n f xs cons sl)
  | [], cons, sl => by unfold seqLoop; exact ok_steps env cons sl
  | (c, l) :: rest, cons, sl => by
    unfold seqLoop
    simp only
    split
    · rename_i hne; exact fun h => absurd h hne
    · rename_i hok
      intro h
      obtain ⟨l1, h1⟩ := IH l c cons sl (by simpa using hok)
      obtain ⟨l2, h2⟩ := seqLoop_steps IH rest _ _ h
      exact ⟨_, h1.trans h2⟩

theorem orLoop_steps {f : Nat} (IH : EvalSteps env data n f) :
    ∀ (cs : List Condition) (loc : Nat) (cons : List Consumption) (sl : Slots),
      StepsOk env cons (orLoop env data n f cs loc cons sl)
  | [], _, cons, sl => by unfold orLoop; exact violation_steps env cons sl (by decide)
  | c :: rest, loc, cons, sl => by
    unfold orLoop
    simp only
    split
    · exact IH loc c cons sl
    · exact orLoop_steps IH rest loc cons _

theorem everyLoop_steps {f : Nat} (IH : EvalSteps env data n f) (c : Condition) :
    ∀ (locs : List Nat) (cons : List Consumption) (sl : Slots),
      StepsOk env cons (everyLoop env data n f c locs cons sl)
  | [], cons, sl => by unfold everyLoop; exact ok_steps env cons sl
  | l :: rest, cons, sl => by
    unfold everyLoop
    simp only
    split
    · exact IH l c cons sl
    · split
      · intro h; simp [sOk, sNotEveryArrayElementPasses] at h
      · rename_i _ hok
        intro h
        obtain ⟨l1, h1⟩ := IH l c cons sl (by simpa using hok)
        obtain ⟨l2, h2⟩ := everyLoop_steps IH c rest _ _ h
        exact ⟨_, h1.trans h2⟩

theorem someLoop_steps {f : Nat} (IH : EvalSteps env data n f) (c : Condition) :
    ∀ (locs : List Nat) (cons : List Consumption) (sl : Slots),
      StepsOk env cons (someLoop env data n f c locs cons sl)
  | [], cons, sl => by unfold someLoop; exact violation_steps env cons sl (by decide)
  | l :: rest, cons, sl => by
    unfold someLoop
    simp only
    split
    · exact IH l c cons sl
    · exact someLoop_steps IH c rest cons _

/-- A Zip passes with consumptions reached from those it started with
    (`base`); `ZipEvery` threads them through the elements. -/
theorem zipLoop_steps {f : Nat} (IH : EvalSteps env data n f) (every : Bool)
    (fields : List Condition) (locss : List (List Nat)) :
    ∀ (k i : Nat) (base cons : List Consumption) (sl : Slots),
      (∃ log, Steps env.balance base log cons) →
      StepsOk env base (zipLoop env data n f every fields locss k i base cons sl)
  | 0, i, base, cons, sl, hb => by
    unfold zipLoop
    split
    · intro _; exact hb
    · exact violation_steps env base sl (by decide)
  | k + 1, i, base, cons, sl, hb => by
    unfold zipLoop
    have hseq := seqLoop_steps env data n IH (fields.zip (locss.map fun ls => ls.getD i 0))
      (if every then cons else base) sl
    cases every
    · simp only [Bool.false_eq_true, ite_false] at hseq ⊢
      split
      · rename_i hrev; intro h; rw [h] at hrev; exact absurd hrev (by decide)
      · split
        · rename_i hok; intro _; exact hseq hok
        · exact zipLoop_steps IH false fields locss k (i + 1) base cons _ hb
    · simp only [ite_true] at hseq ⊢
      split
      · rename_i hrev; intro h; rw [h] at hrev; exact absurd hrev (by decide)
      · split
        · intro h; simp [sOk, sNotEveryZippedElementPasses] at h
        · rename_i hok
          refine zipLoop_steps IH true fields locss k (i + 1) base _ _ ?_
          obtain ⟨l0, h0⟩ := hb
          obtain ⟨l1, h1⟩ := hseq (by simpa using hok)
          exact ⟨_, h0.trans h1⟩

include hcustom in
/-- **A passing evaluation charges by steps.** When `evaluate` passes, the
    consumptions it returns are the input consumptions after successful
    `consume` steps (`hcustom`: a custom checker that fails reports a
    failure status, `EnvOk` in `Bridge`). -/
theorem evalC_steps : ∀ fuel, EvalSteps env data n fuel
  | 0 => fun _ _ cons sl => by unfold evalC; exact violation_steps env cons sl (by decide)
  | f + 1 => by
    have IH := evalC_steps f
    intro loc c cons sl
    unfold evalC
    cases hop : c.operator <;> simp only
    all_goals first
      | exact ok_steps env cons sl
      | exact violation_steps env cons sl (by decide)
      | skip
    case Matches =>
      generalize (if loc > 0 ∧ c.encoding = .AbiEncoded then loc + 32 else loc) = L
      rcases hlc : leadingCheck data L c.compValue with _ | s
      · dsimp only
        rcases hce : childrenE data (L + c.leadingBytes) c with s | _ | locs
        · exact violation_steps env cons sl (childrenE_ne_ok hce)
        · exact violation_steps env cons sl (by decide)
        · dsimp only
          split
          · exact violation_steps env cons sl (by decide)
          · exact seqLoop_steps env data n IH _ cons sl
      · exact violation_steps env cons sl (leadingCheck_ne_ok hlc)
    case And => exact seqLoop_steps env data n IH _ cons sl
    case Or => exact orLoop_steps env data n IH _ loc cons sl
    case Slice =>
      rcases cvAt c.compValue 2 with _ | sz
      · exact violation_steps env cons sl (by decide)
      · dsimp only
        generalize (if c.inlined = true then c.size else load data loc) = len
        generalize (loc + (if c.inlined = true then 0 else 32) + shiftOf c.compValue) = L
        by_cases h1 : c.inlined = false ∧ loc + 32 > data.length
        · rw [if_pos h1]; exact violation_steps env cons sl (by decide)
        · rw [if_neg h1]
          by_cases h2 : shiftOf c.compValue + sz > len
          · rw [if_pos h2]; exact violation_steps env cons sl (by decide)
          · rw [if_neg h2]
            rcases c.children with _ | ⟨ch, _⟩
            · exact violation_steps env cons sl (by decide)
            · exact IH _ _ cons sl
    case Pluck =>
      generalize input data loc c = v
      rcases v with _ | _ | _ | _
      all_goals first
        | exact violation_steps env cons sl (by decide)
        | (dsimp only
           rcases cvAt c.compValue 0 with _ | k
           · exact violation_steps env cons sl (by decide)
           · dsimp only
             split
             · exact violation_steps env cons sl (by decide)
             · exact ok_steps env cons _)
    case Empty => exact result_steps env _ sl (fun _ => ⟨[], .nil cons⟩)
    case ArraySome | ArrayEvery =>
      rcases hce : childrenE data loc c with s | _ | locs
      · exact violation_steps env cons sl (childrenE_ne_ok hce)
      · exact violation_steps env cons sl (by decide)
      · dsimp only
        rcases c.children with _ | ⟨ch, _⟩
        · dsimp only
          split
          · split
            · exact ok_steps env cons sl
            · exact violation_steps env cons sl (by decide)
          · exact violation_steps env cons sl (by decide)
        · dsimp only
          split
          · exact everyLoop_steps env data n IH _ _ cons sl
          · exact someLoop_steps env data n IH _ _ cons sl
    case ArrayTailMatches =>
      rcases hce : childrenE data loc c with s | _ | locs
      · exact violation_steps env cons sl (childrenE_ne_ok hce)
      · exact violation_steps env cons sl (by decide)
      · dsimp only
        split
        · exact violation_steps env cons sl (by decide)
        · exact seqLoop_steps env data n IH _ cons sl
    case ZipSome | ZipEvery =>
      rcases c.children with _ | ⟨t, _⟩
      · exact violation_steps env cons sl (by decide)
      · dsimp only
        rcases hz : zipLocs data n c.compValue t.children sl with s | ⟨locss, len⟩
        · exact violation_steps env cons sl (zipLocs_ne_ok hz)
        · exact zipLoop_steps env data n IH _ _ _ _ 0 cons cons sl ⟨[], .nil cons⟩
    case EqualTo | GreaterThan | LessThan | SignedIntGreaterThan | SignedIntLessThan =>
      split
      · exact violation_steps env cons sl (by decide)
      · exact result_steps env _ sl (fun _ => ⟨[], .nil cons⟩)
    case Bitmask => exact result_steps env _ sl (fun _ => ⟨[], .nil cons⟩)
    case WithinAllowance =>
      split
      · exact violation_steps env cons sl (by decide)
      · exact result_steps env _ sl (allowance_steps env cons _ _)
    case CallWithinAllowance => exact result_steps env _ sl (allowance_steps env cons _ _)
    case WithinRatio => exact result_steps env _ sl (fun _ => ⟨[], .nil cons⟩)
    case Custom =>
      split
      · rename_i s hs
        exact violation_steps env cons sl (hcustom _ _ _ _ _ hs)
      · exact result_steps env _ sl (applyCharges_steps env _ cons)

end


/-! ## One entry per key -/

def keys (c : List Consumption) : List Bytes := c.map (·.key)

/-- One entry per key, each with the accrued balance and not overdrawn. -/
def Good (bal : Bytes → Nat) (c : List Consumption) : Prop :=
  (keys c).Nodup ∧ ∀ e ∈ c, e.balance = bal e.key ∧ e.consumed ≤ e.balance

/-- What the list has consumed from key `k` (0 if the key is untracked). -/
def used (c : List Consumption) (k : Bytes) : Nat :=
  ((c.find? (·.key = k)).map (·.consumed)).getD 0

theorem used_nil (k : Bytes) : used [] k = 0 := rfl

theorem used_cons (e : Consumption) (es : List Consumption) (k : Bytes) :
    used (e :: es) k = if e.key = k then e.consumed else used es k := by
  unfold used; by_cases h : e.key = k <;> simp [List.find?, h]

theorem used_not_mem : ∀ {c : List Consumption} {k : Bytes}, k ∉ keys c → used c k = 0
  | [], _, _ => rfl
  | e :: es, k, h => by
    simp only [keys, List.map_cons, List.mem_cons, not_or] at h
    rw [used_cons, if_neg (fun h' => h.1 h'.symm)]
    exact used_not_mem (by simpa [keys] using h.2)

theorem used_mem : ∀ {c : List Consumption}, (keys c).Nodup → ∀ e ∈ c, used c e.key = e.consumed
  | [], _, _, he => by simp at he
  | e0 :: es, hn, e, he => by
    simp only [keys, List.map_cons, List.nodup_cons] at hn
    rw [used_cons]
    rcases List.mem_cons.mp he with rfl | he
    · simp
    · have hne : e0.key ≠ e.key := fun h => hn.1 (by rw [h]; exact List.mem_map_of_mem he)
      rw [if_neg hne]; exact used_mem hn.2 e he

/-- `consume` keeps one entry per key and adds the amount to key `k`. -/
theorem consume_spec {bal : Bytes → Nat} {env : Env} (hb : env.balance = bal) (k : Bytes) (a : Nat) :
    ∀ {c c' : List Consumption}, Good bal c → consume env c k a = (sOk, c') →
      Good bal c' ∧ (∀ k', k' ∈ keys c' ↔ k' ∈ keys c ∨ k' = k) ∧
      (∀ k', used c' k' = if k' = k then used c k + a else used c k') ∧ a ≤ bal k - used c k
  | [], c', _, h => by
    unfold consume at h
    split at h
    · simp [sAllowanceExceeded, sOk] at h
    · rename_i ha
      simp only [Prod.mk.injEq, true_and] at h
      subst h
      rw [hb] at ha
      refine ⟨⟨by simp [keys], ?_⟩, ?_, ?_, ?_⟩
      · intro e he; simp at he; subst he; simp [hb]; omega
      · intro k'; simp [keys]
      · intro k'; rw [used_cons, used_nil]
        by_cases hk : k' = k
        · subst hk; simp [used_nil]
        · simp [hk, Ne.symm hk]
      · rw [used_nil]; omega
  | e :: es, c', hg, h => by
    have hn := hg.1
    simp only [keys, List.map_cons, List.nodup_cons] at hn
    have he := hg.2 e (by simp)
    unfold consume at h
    by_cases hk : e.key = k
    · rw [if_pos hk] at h
      split at h
      · simp [sAllowanceExceeded, sOk] at h
      · rename_i ha
        simp only [Prod.mk.injEq, true_and] at h
        subst h
        have hused : used (e :: es) k = e.consumed := by rw [used_cons, if_pos hk]
        refine ⟨⟨by simpa [keys] using hn, ?_⟩, ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · simp only; omega
          · exact hg.2 x (List.mem_cons_of_mem _ hx)
        · intro k'; simp only [keys, List.map_cons, List.mem_cons]
          constructor
          · intro h; exact .inl h
          · rintro (h | h)
            · exact h
            · exact .inl (h.trans hk.symm)
        · intro k'
          simp only [used_cons]
          by_cases hk' : k' = k
          · subst hk'; simp [hk]
          · have : e.key ≠ k' := fun h => hk' (h.symm.trans hk)
            simp [this, hk']
        · rw [hused, ← hk]; have h1 := he.1; omega
    · rw [if_neg hk] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h2
      have hg' : Good bal es := ⟨hn.2, fun x hx => hg.2 x (List.mem_cons_of_mem _ hx)⟩
      obtain ⟨hG, hK, hU, hA⟩ := consume_spec hb k a hg' (Prod.ext h1 rfl)
      refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · simp only [keys, List.map_cons, List.nodup_cons]
        refine ⟨?_, hG.1⟩
        intro hm
        rcases (hK e.key).mp hm with h | h
        · exact hn.1 h
        · exact hk h
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he
        · exact hG.2 x hx
      · intro k'; simp only [keys, List.map_cons, List.mem_cons]
        rw [show (k' ∈ List.map (·.key) (consume env es k a).2) = (k' ∈ keys (consume env es k a).2) from rfl,
          hK k']
        simp only [keys]; exact or_assoc.symm
      · intro k'
        rw [used_cons, used_cons, hU k']
        by_cases hk' : k' = k
        · subst hk'; simp [hk]
        · simp [hk', used_cons]
      · rw [used_cons, if_neg hk]; exact hA

/-- The charges to key `k`, as raw spends (`Allowance.Spend`). -/
def charges (log : List (Bytes × Nat)) (k : Bytes) : List Allowance.Spend :=
  (log.filter (fun x => x.1 = k)).map (fun x => .raw x.2)

theorem charges_cons (k0 : Bytes) (a : Nat) (log : List (Bytes × Nat)) (k : Bytes) :
    charges ((k0, a) :: log) k = if k0 = k then .raw a :: charges log k else charges log k := by
  unfold charges; by_cases h : k0 = k <;> simp [List.filter, h]

theorem charges_nil_iff (log : List (Bytes × Nat)) (k : Bytes) :
    charges log k = [] ↔ k ∉ log.map Prod.fst := by
  unfold charges; simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq,
    List.mem_map, not_exists, not_and]

theorem consumeAll_raw (bal used a : Nat) (rest : List Allowance.Spend) (ha : a ≤ bal - used) :
    Allowance.consumeAll bal used (.raw a :: rest) = Allowance.consumeAll bal (used + a) rest := by
  simp only [Allowance.consumeAll, Allowance.charge]
  rw [if_neg (by omega)]

/-- **Steps keep one entry per key.** Along successful steps, the list keeps
    one entry per key with its accrued balance, never overdrawn; its keys
    are those it had and those charged; and for every key the steps are
    `Allowance.consumeAll` on that key's charges. -/
theorem steps_spec {bal : Bytes → Nat} {c c' : List Consumption} {log : List (Bytes × Nat)}
    (h : Steps bal c log c') (hg : Good bal c) :
    Good bal c' ∧ (∀ k, k ∈ keys c' ↔ k ∈ keys c ∨ k ∈ log.map Prod.fst) ∧
      ∀ k, Allowance.consumeAll (bal k) (used c k) (charges log k) = .ok (used c' k) := by
  induction h with
  | nil c =>
    refine ⟨hg, fun k => by simp, fun k => ?_⟩
    simp [charges, Allowance.consumeAll]
  | @step c c1 c2 k0 a log env hb hs _ ih =>
    obtain ⟨hg1, hk1, hu1, ha⟩ := consume_spec hb k0 a hg hs
    obtain ⟨hg2, hk2, hu2⟩ := ih hg1
    refine ⟨hg2, fun k => ?_, fun k => ?_⟩
    · rw [hk2 k, hk1 k]; simp only [List.map_cons, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inl (.inl h)
        · exact .inl (.inr h)
        · exact .inr h
    · rw [charges_cons]
      by_cases hk : k0 = k
      · subst hk
        rw [if_pos rfl, consumeAll_raw _ _ _ _ ha, ← hu2 k0, hu1 k0, if_pos rfl]
      · rw [if_neg hk, ← hu2 k, hu1 k, if_neg (Ne.symm hk)]

/-! ## Settlement -/

/-- `Settlement._persist` on the allowances: every entry, in order, stores
    its accrued balance minus what it consumed, and the accrued timestamp
    (`acc`: `accrue` at the block time). Other keys are left as they are. -/
def persist (acc : Bytes → Allowance.State) :
    (Bytes → Allowance.State) → List Consumption → Bytes → Allowance.State
  | st, [] => st
  | st, e :: es => persist acc
      (fun k => if k = e.key then ⟨e.balance - e.consumed, (acc e.key).timestamp⟩ else st k) es

theorem persist_not_mem (acc : Bytes → Allowance.State) :
    ∀ (st : Bytes → Allowance.State) {c : List Consumption} {k : Bytes}, k ∉ keys c →
      persist acc st c k = st k
  | st, [], _, _ => rfl
  | st, e :: es, k, h => by
    simp only [keys, List.map_cons, List.mem_cons, not_or] at h
    simp only [persist]
    rw [persist_not_mem acc _ (by simpa [keys] using h.2), if_neg h.1]

/-- With one entry per key, each entry is stored once: nothing overwrites it. -/
theorem persist_get (acc : Bytes → Allowance.State) :
    ∀ (st : Bytes → Allowance.State) {c : List Consumption}, (keys c).Nodup → ∀ e ∈ c,
      persist acc st c e.key = ⟨e.balance - e.consumed, (acc e.key).timestamp⟩
  | _, [], _, _, he => by simp at he
  | st, e0 :: es, hn, e, he => by
    simp only [keys, List.map_cons, List.nodup_cons] at hn
    simp only [persist]
    rcases List.mem_cons.mp he with rfl | he
    · rw [persist_not_mem acc _ hn.1, if_pos rfl]
    · exact persist_get acc _ hn.2 e he

/-- **Settlement is one `Allowance.tx` per key.** After evaluations that
    charged `log` (steps from the empty list, balances accrued at `now`),
    `_persist` stores, for every key, exactly what `Allowance.tx` computes
    for that key's charges: the accrued balance minus their sum, or nothing
    for a key not charged. -/
theorem persist_tx (cfg : Bytes → Allowance.Config) (st : Bytes → Allowance.State) (now : Nat)
    {log : List (Bytes × Nat)} {cons : List Consumption}
    (h : Steps (fun k => (Allowance.accrue (cfg k) (st k) now).balance) [] log cons) (k : Bytes) :
    Allowance.tx (cfg k) (st k) now (charges log k) =
      .ok (persist (fun k => Allowance.accrue (cfg k) (st k) now) st cons k) := by
  obtain ⟨hg, hk, hu⟩ := steps_spec h ⟨List.nodup_nil, fun _ he => by simp at he⟩
  have hu := hu k
  rw [used_nil] at hu
  by_cases hm : k ∈ keys cons
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    have hlog : e.key ∈ log.map Prod.fst := by
      rcases (hk e.key).mp hm with h | h
      · simp [keys] at h
      · exact h
    have hne : charges log e.key ≠ [] := fun h => ((charges_nil_iff _ _).mp h) hlog
    rw [persist_get _ st hg.1 e he, used_mem hg.1 e he] at *
    unfold Allowance.tx
    rw [if_neg hne]
    simp only
    rw [hu, (hg.2 e he).1]
  · have hlog : k ∉ log.map Prod.fst := fun h => hm ((hk k).mpr (.inr h))
    rw [(charges_nil_iff _ _).mpr hlog, persist_not_mem _ st hm]
    simp [Allowance.tx]

end EndToEnd
