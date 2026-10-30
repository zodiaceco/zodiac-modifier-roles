import EIP712.Sign
import EIP712.FitCheck
import EIP712.Digest

/-!
# Non-vacuity checks for `EIP712`

1. `hashTypedMessage_spec`: all hypotheses hold on a concrete two-struct
   message with a dynamic (`string`) member. `K` is a constant non-zero
   function here (the theorem is for every `K`; the only fact used about it
   is a non-zero `typeHash`, which keeps kernel evaluation cheap).
2. `Member` (the conclusion of `visit_agree`, `message_agree`,
   `sign_agree`) holds only at offsets the encoder's walk reads: on a struct
   of two words, never at byte 1.
3. `rootB` (`fit`) accepts a permission whose `types` argument is `Pass`
   (unpinned): `sign_agree` then assumes `tys` are the trees the library
   builds; that holds when `types` is pinned.
-/

set_option maxRecDepth 100000

namespace EIP712.NonVacuity
open DecoderFaithfulness DecoderFaithfulness.Roles EIP712

def K : Bytes → Bytes := fun _ => word 1

def defs : Defs :=
  [("EIP712Domain", [⟨"chainId", .atom (.uint 256)⟩]),
   ("Mail", [⟨"n", .atom (.uint 8)⟩, ⟨"s", .string⟩])]

def thD : Bytes := typeHash K defs "EIP712Domain"
def thM : Bytes := typeHash K defs "Mail"

def types : List TNF :=
  [⟨0, .Tuple, thD⟩, ⟨1, .Tuple, thM⟩, ⟨0, .Static, zeros 32⟩,
   ⟨1, .Static, zeros 32⟩, ⟨1, .Dynamic, zeros 32⟩]

def td : TN := ⟨.Tuple, [⟨.Static, [], zeros 32⟩], thD⟩
def tm : TN := ⟨.Tuple, [⟨.Static, [], zeros 32⟩, ⟨.Dynamic, [], zeros 32⟩], thM⟩

def dv : V := .list [.atom (word 1)]
def mv : V := .list [.atom (word 42), .dyn [⟨104, by decide⟩, ⟨105, by decide⟩]]

theorem h0 : toTree types (types.length + 1) 0 = some td := rfl
theorem h1 : toTree types (types.length + 1) 1 = some tm := rfl

theorem thD_ne : typeHash K defs "EIP712Domain" ≠ zeros 32 := by decide +kernel
theorem thM_ne : typeHash K defs "Mail" ≠ zeros 32 := by decide +kernel

theorem hl0 : Lay K defs (.struct "EIP712Domain") td :=
  .struct (by decide) (.cons .atom .nil) (by simp) thD_ne

theorem hl1 : Lay K defs (.struct "Mail") tm :=
  .struct (by decide) (.cons .atom (.cons .string .nil)) (by simp) thM_ne

theorem hdv : HasTy defs (.struct "EIP712Domain") dv :=
  .struct (by decide) (.cons (.atom ⟨by decide +kernel, by decide +kernel⟩) .nil)

theorem hmv : HasTy defs (.struct "Mail") mv :=
  .struct (by decide) (.cons (.atom ⟨by decide +kernel, by decide +kernel⟩) (.cons .string .nil))

/-- All hypotheses of `hashTypedMessage_spec` hold. -/
example : hashTypedMessage K (enc (abiOf defs (.struct "EIP712Domain") dv))
    (enc (abiOf defs (.struct "Mail") mv)) types = some (digest K defs "Mail" dv mv) :=
  hashTypedMessage_spec K defs "Mail" types dv mv td tm h0 hl0 h1 hl1 hdv hmv
    (by decide +kernel) (by decide +kernel)

/-! ## 2. Only the encoder's offsets are members

A 64-byte view of one struct of two `uint256` words. The encoder's walk of
that struct reads its members at 0 and 32 only, so no node can be a
`Member` (or a `Window` base) at byte 1. (The statement review found that
`Member` used to ask only for *some* type tree read at the offset, which
held at byte 1; it now requires `Reach`, the encoder's walk from the
argument's type tree.) -/

def pair : TN := ⟨.Tuple, [⟨.Static, [], zeros 32⟩, ⟨.Static, [], zeros 32⟩], zeros 32⟩

theorem pair_locs : childLocs (view (zeros 64) 0 64) pair 0 = some [0, 32] := by decide +kernel

theorem reach_pair {t : TN} {r : Nat} (h : Reach (view (zeros 64) 0 64) pair t r) : r = 0 ∨ r = 32 := by
  have key : ∀ t r, Reach (view (zeros 64) 0 64) pair t r →
      (t = pair ∧ r = 0) ∨ (t = ⟨.Static, [], zeros 32⟩ ∧ (r = 0 ∨ r = 32)) := by
    intro t r h
    induction h with
    | root => exact Or.inl ⟨rfl, rfl⟩
    | @child t r locs k _ hcl hk ih =>
      rcases ih with ⟨rfl, rfl⟩ | ⟨rfl, _⟩
      · rw [pair_locs] at hcl
        cases hcl
        right
        have : k = 0 ∨ k = 1 := by simp at hk; omega
        rcases this with rfl | rfl <;> simp [pair]
      · simp [childLocs] at hcl
  rcases key t r h with ⟨_, rfl⟩ | ⟨_, h⟩
  · exact Or.inl rfl
  · exact h

example (Γ : Plucks) (d : Condition) : ¬ Member Γ (zeros 64) 0 64 pair d 1 := by
  rintro ⟨t, _, r, _, hR, hl, _⟩
  rcases reach_pair hR with h | h <;> omega

/-! ## 3. `fit` accepts an unpinned `types` argument

`sign_agree` takes the type trees `tys` as given. That they are what the
library builds from the calldata's `types` holds when the permission pins
`types` (the SDK's `allowSignTypedMessage` does; a permission lint should
flag it otherwise). `rootB` itself does not require it: -/

def pass : Condition := ⟨.Dynamic, .Pass, [], false, 0, 0, []⟩
def argD : Condition := ⟨.AbiEncoded, .Matches, [⟨.Static, .Pass, [], true, 32, 0, []⟩], false, 0, 0, []⟩
def argM : Condition := ⟨.AbiEncoded, .Matches,
  [⟨.Static, .Pass, [], true, 32, 0, []⟩, ⟨.Dynamic, .Pass, [], false, 0, 0, []⟩], false, 0, 0, []⟩
def root : Condition := ⟨.AbiEncoded, .Matches, [argD, argM, pass], false, 0, 4, []⟩

example : rootB (fun _ => none) root td tm = true := by decide +kernel

end EIP712.NonVacuity
