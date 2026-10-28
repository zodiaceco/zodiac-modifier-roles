import EIP712.Agree

/-!
# The whole `signTypedMessage` condition, Zip jumps included

`Eval` (`DecoderFaithfulness.Roles`) is every node `evaluate` reaches from
the root: `Visit`, plus the jumps of `ZipSome` / `ZipEvery` to the arrays
that `Pluck` nodes stored. A Zip may read a Pluck anywhere in the tree, so
this theorem starts at the root of the permission: a `Matches` on the
calldata of `signTypedMessage(bytes domain, bytes message, types)`.

`sign_agree`: when the `domain` and `message` conditions follow their type
trees (`MsgFit`, with one pluck table `Γ` for both) and the `types`
condition has no `Pluck` / `Zip`, every node `evaluate` reaches is the
root, one of its three children, a node below `types`, or sits at a member
(or a window of a member) the encoder read in `domain` or `message`, in
the argument its path starts with.
-/

namespace EIP712
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- No node of the tree is a `Pluck` or a `Zip`. -/
inductive NoPZ : Condition → Prop
  | mk {c} : c.operator ≠ .Pluck → c.operator ≠ .ZipSome → c.operator ≠ .ZipEvery →
      (∀ ch ∈ c.children, NoPZ ch) → NoPZ c

theorem noPZ_default : NoPZ default :=
  .mk (by decide) (by decide) (by decide) (fun _ h => absurd h List.not_mem_nil)

theorem noPZ_getD {c : Condition} (h : NoPZ c) (i : Nat) : NoPZ (c.children.getD i default) := by
  cases h with
  | mk _ _ _ hc =>
    by_cases hi : i < c.children.length
    · have : c.children.getD i default = c.children[i] := by
        simp [List.getD_eq_getElem?_getD, hi]
      rw [this]; exact hc _ (List.getElem_mem hi)
    · have : c.children.getD i default = default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : c.children.length ≤ i)]
      rw [this]; exact noPZ_default

theorem noPZ_headD {c : Condition} (h : NoPZ c) : NoPZ (c.children.headD default) := by
  have := noPZ_getD h 0
  cases hc : c.children with
  | nil => exact noPZ_default
  | cons x xs => rw [hc] at this; simpa using this

theorem noPZ_withSize {c : Condition} (n : Nat) (h : NoPZ c) : NoPZ (c.withSize n) := by
  cases h with
  | mk h1 h2 h3 h4 => exact .mk h1 h2 h3 h4

theorem noPZ_visit {data : Bytes} {c : Condition} {loc : Nat} {p : List Nat} {d : Condition}
    {l : Nat} (hv : Visit data c loc p d l) : NoPZ c → NoPZ d := by
  induction hv with
  | here => exact id
  | logical ch _ hmem _ ih =>
    intro h; cases h with
    | mk _ _ _ hc => exact ih (hc ch hmem)
  | matchesChild _ i _ _ _ _ _ ih => intro h; exact ih (noPZ_getD h i)
  | arrayIter _ _ _ _ _ _ ih => intro h; exact ih (noPZ_headD h)
  | arrayTail locs j _ _ _ _ _ _ ih => intro h; exact ih (noPZ_getD h _)
  | slice _ _ _ _ ih => intro h; exact ih (noPZ_withSize _ (noPZ_headD h))

/-- Where `SignTypedMessageLib`'s fallback finds argument `j`:
    `calldataload(4 + 32 j) + 4` (the content follows its length word). -/
def argAt (data : Bytes) (j : Nat) : Nat := load data (4 + 32 * j) + 4

/-- The root's `children`: the `domain` and `message` slots are offsets
    (not inlined), so Roles finds them at the tail locations of the first
    two head words. -/
theorem root_locs {data : Bytes} {root : Condition} {locs : List Nat}
    (h3 : root.children.length = 3) (h0 : (root.children.getD 0 default).inlined = false)
    (h1 : (root.children.getD 1 default).inlined = false)
    (hc : childrenLoop data 4 (fun i => root.children.getD i default) 3 0 0 = some locs) :
    ∃ L0 L1 rest, locs = L0 :: L1 :: rest ∧ tailLocation data 4 (32 * 0) = L0 ∧
      L0 ≤ data.length ∧ tailLocation data 4 (32 * 1) = L1 ∧ L1 ≤ data.length := by
  simp only [childrenLoop, h0, h1, Bool.false_eq_true, ite_false] at hc
  split at hc
  · simp at hc
  · rename_i hb0
    split at hc
    · simp at hc
    · rename_i hb1
      rw [Option.map_eq_some_iff] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      rw [Option.map_eq_some_iff] at hx
      obtain ⟨y, _, rfl⟩ := hx
      exact ⟨_, _, y, rfl, rfl, by omega, rfl, by omega⟩

/-- The pluck table and the type trees of `domain` (`j = 0`) and the
    primary type (`j = 1`) fit the root of the permission. -/
structure RootFit (Γ : Plucks) (root : Condition) (tys : Nat → TN) : Prop where
  op : root.operator = .Matches
  enc : root.encoding = .AbiEncoded
  lb : root.leadingBytes = 4
  len : root.children.length = 3
  offset : ∀ j, j < 2 → (root.children.getD j default).inlined = false
  args : ∀ j, j < 2 → MsgFit Γ (root.children.getD j default) (tys j)
  types : NoPZ (root.children.getD 2 default)

/-- **Every node `evaluate` reaches from the root of a `signTypedMessage`
    permission, Zip jumps included, on any calldata**: the root, one of its
    children, a node below `types` (`NoPZ`), or a node at path `j :: q`
    that sits at a member of argument `j` (`domain` or `message`) the
    encoder read, or reads a window inside one. `ms j` is the length the
    library uses for argument `j`, `tys j` its type tree, and the encoder's
    walk of both arguments succeeded. The member is the one the encoder's
    walk of `tys j` reads, by its path from the argument root (`Reach`).
    `tys` is taken as given: it is the type tree the library builds only
    when the permission pins `types` (`RootFit` does not require that). -/
theorem sign_agree (Γ : Plucks) (data : Bytes) (root : Condition) (tys : Nat → TN)
    (ms : Nat → Nat) (hroot : RootFit Γ root tys)
    (hread : ∀ j, j < 2 → ∃ fuel v,
      readV (view data (argAt data j + 32) (ms j)) fuel (tys j) 0 = some v)
    {p : List Nat} {d : Condition} {l : Nat} (he : Eval data root p d l) :
    (p = [] ∧ d = root) ∨ (∃ j, j < 2 ∧ p = [j] ∧ d = root.children.getD j default) ∨
    (∃ q, p = 2 :: q ∧ NoPZ d) ∨
    (∃ j q, j < 2 ∧ p = j :: q ∧ q ≠ [] ∧ Site Γ data (argAt data j + 32) (ms j) (tys j) d l) := by
  induction he with
  | @visit p d l hv =>
    cases hv with
    | here => exact Or.inl ⟨rfl, rfl⟩
    | logical _ hop' => have := hroot.op; rcases hop' with h | h <;> simp_all
    | @matchesChild _ _ p' _ _ locs i hi _ hch hl hv' =>
      rw [if_neg (by simp), hroot.lb, Nat.zero_add] at hch
      unfold children at hch
      rw [if_neg (by rw [hroot.enc]; decide), hroot.len] at hch
      obtain ⟨L0, L1, rest, rfl, ht0, hb0, ht1, hb1⟩ :=
        root_locs hroot.len (hroot.offset 0 (by decide)) (hroot.offset 1 (by decide)) hch
      have hi3 : i < 3 := by rw [← hl, hroot.len] at hi; simpa using hi
      -- argument `j` (`domain` / `message`): where the library reads it
      have harg : ∀ j, j < 2 → ∀ L, tailLocation data 4 (32 * j) = L → L ≤ data.length →
          Visit data (root.children.getD j default) L p' d l →
          (∃ j', j' < 2 ∧ j :: p' = [j'] ∧ d = root.children.getD j' default) ∨
          (∃ j' q, j' < 2 ∧ j :: p' = j' :: q ∧ q ≠ [] ∧
            Site Γ data (argAt data j' + 32) (ms j') (tys j') d l) := by
        intro j hj L ht hb hv
        have hLa : L = argAt data j := fallback_offset data j L ht hb
        obtain ⟨fuel, v, hr⟩ := hread j hj
        rw [← hLa] at hr
        rcases message_agree Γ data L (ms j) (hroot.args j hj) (by rw [hLa, argAt]; omega) hr hv
          with ⟨rfl, rfl⟩ | ⟨hp, hs⟩
        · exact Or.inl ⟨j, hj, rfl, rfl⟩
        · exact Or.inr ⟨j, p', hj, rfl, hp, by rw [← hLa]; exact hs⟩
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · simp only [List.getElem_cons_zero] at hv'
        exact Or.inr ((harg 0 (by decide) L0 ht0 hb0 hv').elim (Or.inl) (fun h => Or.inr (Or.inr h)))
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hv'
        exact Or.inr ((harg 1 (by decide) L1 ht1 hb1 hv').elim (Or.inl) (fun h => Or.inr (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inl ⟨p', rfl, noPZ_visit hv' hroot.types⟩))
    | arrayIter _ _ _ hop' => have := hroot.op; rcases hop' with h | h <;> simp_all
    | arrayTail _ _ _ hop' => have := hroot.op; simp_all
    | slice hop' => have := hroot.op; simp_all
  | @zip pz z lz pp pk L p d l f locs i hi _ hzop hf _ hpkop hslot hch hv' ihz ihpk =>
    -- the Zip's field `f` follows the element type of the slot it reads
    have hzfit : ∃ lf, Γ (cvByte z.compValue f) = some lf ∧
        MetaFit ((zipFields z).getD f default) lf ∧ FitT Γ ((zipFields z).getD f default) lf := by
      rcases ihz with ⟨_, rfl⟩ | ⟨j, hj, _, rfl⟩ | ⟨q, _, hnz⟩ | ⟨j, q, hj, _, _, hsite⟩
      · have := hroot.op; rcases hzop with h | h <;> simp_all
      · have := (hroot.args j hj).op; rcases hzop with h | h <;> simp_all
      · cases hnz; rcases hzop with h | h <;> simp_all
      · rcases hsite with ⟨t, _, _, _, _, _, hfit, _, _⟩ | ⟨hw, _⟩
        · cases hfit with
          | zip _ hex hall =>
            obtain ⟨lf, hg, hm⟩ := hex f hf
            exact ⟨lf, hg, hm, hall f lf hf hg⟩
          | leaf hn => rcases hzop with h | h <;> simp_all [NoDescend]
          | logical hop => rcases hzop with h | h <;> rcases hop with h' | h' <;> simp_all
          | array _ _ _ hop =>
            rcases hzop with h | h <;> rcases hop with h' | h' | h' | h' <;> simp_all
          | _ => rcases hzop with h | h <;> simp_all
        · cases hw <;> rcases hzop with h | h <;> simp_all [NoDescend]
    obtain ⟨lf, hg, hmeta, hft⟩ := hzfit
    -- the Pluck it reads sits on an array of that element type
    rcases ihpk with ⟨_, rfl⟩ | ⟨j, hj, _, rfl⟩ | ⟨q, _, hnz⟩ | ⟨j, q, hj, rfl, hq, hsite⟩
    · have := hroot.op; simp_all
    · have := (hroot.args j hj).op; simp_all
    · cases hnz; simp_all
    · rcases hsite with ⟨t, fuel, r, v, hR, hL, hfit, hread', _⟩ | ⟨hw, _⟩
      · cases hfit with
        | pluck _ hpl =>
          obtain ⟨th, rfl⟩ := hpl lf (by rw [hslot]; exact hg)
          obtain ⟨fu, rfl⟩ := readV_succ hread'
          rw [hL] at hch
          obtain ⟨elocs, vs, rfl, rfl, hcl, hel, hk⟩ :=
            children_agree_array (c := zipStub ((zipFields z).getD f default)) hread' rfl
              (by simpa [zipStub] using hmeta) locs hch
          have hi' : i < elocs.length := by simpa using hi
          have hR' : Reach (view data (argAt data j + 32) (ms j)) (tys j) lf elocs[i] := by
            simpa using Reach.child (k := i) hR hcl hi'
          refine Or.inr (Or.inr (Or.inr ⟨j, q ++ i :: p, hj, by simp, by simp, ?_⟩))
          exact visit_agree Γ data _ _ (tys j) hv'
            (Or.inl ⟨lf, fu, _, _, hR', by simp, hft, hk i hi' (by omega), Or.inl hmeta⟩)
        | leaf hn => simp_all [NoDescend]
        | _ => simp_all [IsZip]
      · cases hw <;> simp_all [NoDescend]

end EIP712
