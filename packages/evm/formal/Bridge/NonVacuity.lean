import Bridge.Pipeline
import Bridge.InvCheck
import ConditionCheck.Flat

/-!
# Non-vacuity of `sdk_pipeline`

A concrete instance where every hypothesis of `sdk_pipeline` holds on a
tree that normalization actually rewrites, and the conclusion says
something: the reading of the tree as written passes on one calldata and
fails on another.

`f(uint256 a, uint256 b)` with the user tree

    c0 = Or[Matches:AbiEncoded[EqualTo(1), Pass], Matches:AbiEncoded[EqualTo(2), Pass]]

`pushDownOr` merges it into `nc = Matches:AbiEncoded[Or[EqualTo(1), EqualTo(2)], Pass]`
(`normalize 1` and `normalize 3`). `fs` is its BFS flattening. Checked:

* `inv [] c0` (through `invB_sound`, by kernel `decide`);
* `Packable fs` (through `packableB_sound`), `nest fs 0 = nc`;
* `normalize k c0 = nc` for `k = 1` and `k = 3`;
* the contract's evaluation of the stored tree does not revert on
  `dataOk = sel ++ word 2 ++ word 0` (passes) nor on
  `dataBad = sel ++ word 3 ++ word 0` (fails with `OrViolation`);
* hence, by `sdk_pipeline`, the reading of `c0` passes on `dataOk` and fails
  on `dataBad`.

No `native_decide`.
-/

namespace Bridge.NonVacuity
open Bridge Normalize DecoderFaithfulness DecoderFaithfulness.Roles ConditionPacking Evaluate

def w (n : Nat) : List Nat := List.replicate 31 0 ++ [n]
def wb (n : Nat) : Bytes := (w n).map fun k => ⟨k % 256, Nat.mod_lt _ (by decide)⟩
def eq1 : Cond := ⟨1, 16, w 1, []⟩
def eq2 : Cond := ⟨1, 16, w 2, []⟩
def pass1 : Cond := ⟨1, 0, [], []⟩
def mt (x : Cond) : Cond := ⟨5, 5, [], [x, pass1]⟩
/-- The user's tree. -/
def c0 : Cond := ⟨0, 2, [], [mt eq1, mt eq2]⟩
def orN : Cond := ⟨0, 2, [], [eq1, eq2]⟩
/-- The normalized tree. -/
def nc : Cond := ⟨5, 5, [], [orN, pass1]⟩
/-- Its BFS flattening. -/
def fs : List Flat :=
  [⟨0, .AbiEncoded, .Matches, []⟩, ⟨0, .None, .Or, []⟩, ⟨0, .Static, .Pass, []⟩,
   ⟨1, .Static, .EqualTo, wb 1⟩, ⟨1, .Static, .EqualTo, wb 2⟩]

def env0 : Env := ⟨0, fun _ => 0, fun _ _ => (1, 0), fun _ _ _ _ => .inl 1, fun _ _ => 1⟩
def sel : Bytes := [0, 0, 0, 0]
def dataOk : Calldata := sel ++ wb 2 ++ wb 0
def dataBad : Calldata := sel ++ wb 3 ++ wb 0

theorem env0_ok : EnvOk env0 := ⟨fun _ _ _ _ s h => by cases h; decide⟩

/-! ## The hypotheses -/

theorem c0_inv : inv [] c0 := invB_sound [] (by decide +kernel)
theorem fs_packable : Packable fs := ConditionCheck.packableB_sound (by decide +kernel)
theorem fs_nest : nest fs 0 = nc := by decide +kernel
theorem norm1 : normalize 1 c0 = nc := by decide +kernel

theorem sortCh_eq : sortCh [eq1, eq2] = [eq1, eq2] := by
  unfold sortCh; simp; decide +kernel

theorem n1or : normalize 1 orN = orN := by
  rw [normalize]
  have h : keepsAsWritten orN = false := by decide
  simp only [h, Bool.false_eq_true, ite_false]
  have e : unwrap (dedupe (flatten { orN with ch := orN.ch.map (normalize 0) })) = orN := by
    decide +kernel
  have p : pushStep orN = none := by decide +kernel
  rw [e, pushDownOr, p]; simp only
  unfold sortB; rw [if_pos (by decide +kernel)]
  show (⟨0, 2, [], sortCh [eq1, eq2]⟩ : Cond) = orN
  rw [sortCh_eq]; rfl

theorem n2nc : normalize 2 nc = nc := by
  rw [normalize]
  have h : keepsAsWritten nc = false := by decide
  simp only [h, Bool.false_eq_true, ite_false]
  have hc : nc.ch.map (normalize 1) = nc.ch := by
    show [normalize 1 orN, normalize 1 pass1] = [orN, pass1]
    rw [n1or]; decide +kernel
  rw [hc]
  decide +kernel

theorem n2m (x : Cond) (hx : x = eq1 ∨ x = eq2) : normalize 2 (mt x) = mt x := by
  rcases hx with rfl | rfl <;> decide +kernel

theorem norm3 : normalize 3 c0 = nc := by
  rw [normalize]
  have h : keepsAsWritten c0 = false := by decide
  simp only [h, Bool.false_eq_true, ite_false]
  have hc : c0.ch.map (normalize 2) = c0.ch := by
    show [normalize 2 (mt eq1), normalize 2 (mt eq2)] = [mt eq1, mt eq2]
    rw [n2m _ (.inl rfl), n2m _ (.inr rfl)]
  rw [hc]
  have e : unwrap (dedupe (flatten { c0 with ch := c0.ch })) = c0 := by decide +kernel
  have p : pushStep c0 = some nc := by decide +kernel
  rw [e, pushDownOr, p]; simp only
  rw [n2nc]; decide +kernel

/-! ## The stored tree runs without reverting -/

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem run_ok : (run env0 dataOk (D [] nc) (maxPluck fs) []).status = sOk := by
  simp (config := {decide := true}) [run, D, nc, orN, eq1, eq2, pass1, toRoles, toRolesL,
    DecoderFaithfulness.annotate_eq, evalC, seqLoop, orLoop, opN, encN, ConditionPacking.opOf?,
    ConditionPacking.encOf?, cvOf, lbOf, Roles.isInlined, Roles.inlinedSize, leadingCheck, childrenE,
    depth, depthL, maxPluck, fs, Roles.children, inlinedSizeLoop, wordVal, toBytes, w, allocPanics,
    dataOk, sel, wb, childrenLoop, input, load, inputB, cvB, Evaluate.compare, result, key, zeros, ok,
    violation]

theorem run_bad : (run env0 dataBad (D [] nc) (maxPluck fs) []).status = sOrViolation := by
  simp (config := {decide := true}) [run, D, nc, orN, eq1, eq2, pass1, toRoles, toRolesL,
    DecoderFaithfulness.annotate_eq, evalC, seqLoop, orLoop, opN, encN, ConditionPacking.opOf?,
    ConditionPacking.encOf?, cvOf, lbOf, Roles.isInlined, Roles.inlinedSize, leadingCheck, childrenE,
    depth, depthL, maxPluck, fs, Roles.children, inlinedSizeLoop, wordVal, toBytes, w, allocPanics,
    dataBad, sel, wb, childrenLoop, input, load, inputB, cvB, Evaluate.compare, result, key, zeros, ok,
    violation, sOrViolation]

/-! ## `sdk_pipeline` applies, and its conclusion has content -/

theorem unpack_fs (junk junk' : Mem) :
    unpack [] (bufMem (pack junk fs) junk') = some (D [] nc, maxPluck fs) := by
  rw [pack_roundtrip [] junk junk' fs fs_packable, unpacked_eq [] fs fs_packable 0, fs_nest]

/-- The reading of the tree as written passes on `dataOk`. -/
theorem reading_passes (junk junk' : Mem) :
    (sem (readWorld [] env0 dataOk (maxPluck fs)) c0 (.pos 0) Slots.empty (toMap [])).1 =
      some (toMap (run env0 dataOk (D [] nc) (maxPluck fs) []).cons) := by
  have h := sdk_pipeline [] env0 env0_ok dataOk c0 c0_inv 3 fs fs_packable (fs_nest.trans norm3.symm)
    junk junk' (unpack_fs junk junk') [] (by rw [run_ok]; decide)
  have h2 := h.2
  rw [if_pos run_ok] at h2
  exact h2

/-- The reading of the tree as written fails on `dataBad`. -/
theorem reading_fails (junk junk' : Mem) :
    (sem (readWorld [] env0 dataBad (maxPluck fs)) c0 (.pos 0) Slots.empty (toMap [])).1 = none := by
  have h := sdk_pipeline [] env0 env0_ok dataBad c0 c0_inv 3 fs fs_packable (fs_nest.trans norm3.symm)
    junk junk' (unpack_fs junk junk') [] (by rw [run_bad]; decide)
  have h2 := h.2
  rw [if_neg (by rw [run_bad]; decide)] at h2
  exact h2.2

end Bridge.NonVacuity
