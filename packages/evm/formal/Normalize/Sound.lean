import Normalize.Steps
import Normalize.PushDown

/-!
# Normalization keeps the meaning

`normalize_sound`: for every world satisfying `World.Ok`, and every
condition satisfying an invariant under which the world reads normalized
children and merged `Or`s as the originals (`World.NormOk`), every fuel:
`normalize n c` means the same as `c`: on every decoded
value, slots and consumptions it passes or fails alike, ends with the same
slots, and charges the same allowances.
-/

namespace Normalize

section
variable {V S C Ch : Type} {W : World V S C} {step : C → Ch → Option C}

theorem normalize_same (hW : W.Ok step) {inv : Cond → Prop} (hN : W.NormOk inv) :
    ∀ (n : Nat) (c : Cond), inv c → Same W (normalize n c) c
  | 0, c, _ => Same.refl c
  | n + 1, c, hc => by
    have ih := normalize_same hW hN n
    rw [normalize]
    by_cases hk : keepsAsWritten c = true
    · rw [if_pos hk]; exact Same.refl c
    rw [if_neg hk]
    have hk' : keepsAsWritten c = false := by simpa using hk
    have hsub := hN.sub c hc
    have h1 : Same W { c with ch := c.ch.map (normalize n) } c :=
      same_congr c (Pw.of_map fun x hx => ih x (hsub x hx))
        (fun v => hN.fields n c.enc c.cv c.ch hsub v) (hN.ext n c hc hk')
    exact (sortB_same hW _).trans <| (pushDownOr_same hW hN (fun x hx => ih x hx) _
      (hN.pre n c hc hk')).trans <| (unwrap_same _).trans <|
      (dedupe_same hW _).trans <| (flatten_same _).trans h1

/-- **Normalization never changes what a condition means.** -/
theorem normalize_sound (hW : W.Ok step) {inv : Cond → Prop} (hN : W.NormOk inv) (n : Nat)
    (c : Cond) (hc : inv c) : sem W (normalize n c) = sem W c :=
  (normalize_same hW hN n c hc).1

end

/-! ## The allowance charges of the contract commute

`AllowanceConsumer.consume`: a charge of `a` on key `k` passes if
`a ≤ balance(k) − consumed(k)` and then adds `a` to `consumed(k)`. The
balances are fixed for the transaction (accrued once, at the first charge of
a key). -/

def consume {K : Type} [DecidableEq K] (bal : K → Nat) (cs : K → Nat) (x : K × Nat) :
    Option (K → Nat) :=
  if x.2 ≤ bal x.1 - cs x.1 then some fun k => if k = x.1 then cs k + x.2 else cs k else none

theorem consume_comm {K : Type} [DecidableEq K] (bal : K → Nat) (cs : K → Nat) (x y : K × Nat) :
    (consume bal cs x).bind (consume bal · y) = (consume bal cs y).bind (consume bal · x) := by
  rcases x with ⟨k1, a⟩
  rcases y with ⟨k2, b⟩
  unfold consume
  by_cases hk : k1 = k2
  · subst hk
    by_cases h1 : a ≤ bal k1 - cs k1 <;> by_cases h2 : b ≤ bal k1 - cs k1 <;>
      simp only [h1, h2, Option.bind_some, Option.bind_none, ↓reduceIte]
    · by_cases h3 : b ≤ bal k1 - (cs k1 + a) <;> by_cases h4 : a ≤ bal k1 - (cs k1 + b) <;>
        simp only [h3, h4, ite_true, ite_false]
      · congr 1; funext k; by_cases hk : k = k1 <;> simp [hk]; omega
      · omega
      · omega
    · have : ¬b ≤ bal k1 - (cs k1 + a) := by omega
      simp [this]
    · have : ¬a ≤ bal k1 - (cs k1 + b) := by omega
      simp [this]
  · have hne : k2 ≠ k1 := fun h => hk h.symm
    by_cases h1 : a ≤ bal k1 - cs k1 <;> by_cases h2 : b ≤ bal k2 - cs k2 <;>
      simp [h1, h2, hk, hne]
    congr 1
    funext k
    by_cases e1 : k = k1 <;> by_cases e2 : k = k2 <;> simp_all

end Normalize
