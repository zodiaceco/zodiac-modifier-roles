import EIP712.Read

/-!
# The encoder hashes, by the spec, exactly what it reads

`hashField_spec`: on any bytes, for the type tree of any EIP-712 type, the
contract's `_hashField` reverts exactly when `readV` fails, and otherwise
returns `encV` (EIP-712 `enc`, `hashStruct` for a struct) of the value
`readV` read. Nothing is assumed of the bytes or of `K`.
-/

namespace EIP712
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- The two loops walk in lockstep: if the child hash is `E k` of the child
    value at every step, the block's hashes are `E k` of the values read. -/
theorem blockLoop_map {α β : Type} (data : Bytes) (hf : TN → Nat → Option α)
    (rf : TN → Nat → Option β) (E : Nat → β → α) (cs : List TN) (isArray : Bool) (bl : Nat) :
    ∀ n i h, (∀ k, k < n → ∀ loc,
      hf (cs.getD (if isArray then 0 else i + k) default) loc =
        (rf (cs.getD (if isArray then 0 else i + k) default) loc).map (E (i + k))) →
    blockLoop data hf cs isArray bl n i h =
      (blockLoop data rf cs isArray bl n i h).map (fun vs => vs.mapIdx fun k v => E (i + k) v)
  | 0, _, _, _ => by simp [blockLoop]
  | n + 1, i, h, hyp => by
    simp only [blockLoop]
    split
    · simp
    · rename_i loc isz _
      have h0 := hyp 0 (by omega) loc
      simp only [Nat.add_zero] at h0
      rw [h0]
      cases hr : rf (cs.getD (if isArray = true then 0 else i) default) loc with
      | none => simp
      | some v =>
        simp only [Option.map_some]
        have ih := blockLoop_map data hf rf E cs isArray bl n (i + 1)
          (h + if isz > 0 then isz else 32) (by
            intro k hk loc'
            have := hyp (k + 1) (by omega) loc'
            rw [show i + 1 + k = i + (k + 1) by omega]
            exact this)
        rw [ih]
        cases blockLoop data rf cs isArray bl n (i + 1) (h + if isz > 0 then isz else 32) with
        | none => simp
        | some vs =>
          simp only [Option.map_some, List.mapIdx_cons, Nat.add_zero, Option.some.injEq,
            List.cons.injEq, true_and]
          congr 1
          funext k v
          rw [show i + 1 + k = i + (k + 1) by omega]

theorem blockLoop_length {α : Type} (data : Bytes) (hf : TN → Nat → Option α) (cs : List TN)
    (isArray : Bool) (bl : Nat) :
    ∀ n i h vs, blockLoop data hf cs isArray bl n i h = some vs → vs.length = n
  | 0, _, _, vs, e => by simp [blockLoop] at e; simp [← e]
  | n + 1, i, h, vs, e => by
    simp only [blockLoop] at e
    cases hc : childLocation data bl h (cs.getD (if isArray = true then 0 else i) default) with
    | none => rw [hc] at e; simp at e
    | some p =>
      obtain ⟨loc, isz⟩ := p
      rw [hc] at e
      simp only at e
      cases hr : hf (cs.getD (if isArray = true then 0 else i) default) loc with
      | none => rw [hr] at e; simp at e
      | some r =>
        rw [hr] at e
        simp only at e
        cases hb : blockLoop data hf cs isArray bl n (i + 1) (h + if isz > 0 then isz else 32) with
        | none => rw [hb] at e; simp at e
        | some ws =>
          rw [hb] at e
          simp at e
          rw [← e]
          simp [blockLoop_length data hf cs isArray bl n _ _ ws hb]

theorem flatten_fields (K : Bytes → Bytes) (defs : Defs) :
    ∀ (tys : List Ty) (vs : List V), vs.length ≤ tys.length →
    (vs.mapIdx fun k v => encV K defs (tys.getD k default) v).flatten = encFields K defs tys vs
  | _, [], _ => by simp [encFields]
  | [], _ :: _, h => by simp at h
  | t :: ts, v :: vs, h => by
    simp only [List.mapIdx_cons, List.getD_cons_zero, List.flatten_cons, encFields]
    congr 1
    have := flatten_fields K defs ts vs (by simp at h; omega)
    rw [← this]
    congr 2

theorem flatten_same (K : Bytes → Bytes) (defs : Defs) (t : Ty) :
    ∀ (vs : List V), (vs.mapIdx fun _ v => encV K defs t v).flatten = encSame K defs t vs
  | [] => by simp [encSame]
  | v :: vs => by
    simp only [List.mapIdx_cons, List.flatten_cons, encSame]
    rw [flatten_same K defs t vs]

theorem LayL.length {K : Bytes → Bytes} {defs : Defs} :
    ∀ {tys ls}, LayL K defs tys ls → tys.length = ls.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [LayL.length h]

theorem LayL.get {K : Bytes → Bytes} {defs : Defs} :
    ∀ {tys ls}, LayL K defs tys ls → ∀ k, k < ls.length →
      Lay K defs (tys.getD k default) (ls.getD k default)
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons h _, 0, _ => by simpa using h
  | _, _, .cons _ hs, k + 1, hk => by simpa using LayL.get hs k (by simp at hk; omega)

/-- **The encoder is the EIP-712 spec applied to what it reads**, on any
    bytes: `_hashField` reverts iff the walk fails, and otherwise returns
    `enc` of the value read. -/
theorem hashField_spec (K : Bytes → Bytes) (defs : Defs) (data : Bytes) :
    ∀ (fuel : Nat) {ty : Ty} {t : TN} (loc : Nat), Lay K defs ty t →
    hashField K data fuel t loc = (readV data fuel t loc).map (encV K defs ty)
  | 0, _, _, _, _ => by simp [hashField, readV]
  | fuel + 1, ty, t, loc, hl => by
    cases hl with
    | atom =>
      simp only [hashField, readV, ite_true]
      cases wordAt data loc <;> simp [encV]
    | bytes =>
      simp only [hashField, readV]
      simp only [show (Encoding.Dynamic = Encoding.Static) = False by simp, ite_false, ite_true]
      cases wordAt data loc with
      | none => simp
      | some w => simp only; split <;> simp [encV]
    | string =>
      simp only [hashField, readV]
      simp only [show (Encoding.Dynamic = Encoding.Static) = False by simp, ite_false, ite_true]
      cases wordAt data loc with
      | none => simp
      | some w => simp only; split <;> simp [encV]
    | @struct s ls hdef hls hne hth =>
      simp only [hashField, readV, hashBlock]
      simp only [show (Encoding.Tuple = Encoding.Static) = False by simp,
        show (Encoding.Tuple = Encoding.Dynamic) = False by simp,
        show (Encoding.Tuple = Encoding.Array) = False by simp, ite_false, ite_true,
        Bool.false_eq_true, false_and]
      have hmap := blockLoop_map data (hashField K data fuel) (readV data fuel)
        (fun k v => encV K defs (((fieldsOf defs s).map (·.ty)).getD k default) v) ls false loc
        ls.length 0 0 (by
          intro k hk loc'
          simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
          exact hashField_spec K defs data fuel loc' (LayL.get hls k hk))
      rw [hmap]
      cases hb : blockLoop data (readV data fuel) ls false loc ls.length 0 0 with
      | none => simp
      | some vs =>
        have hlen := blockLoop_length data _ ls false loc ls.length 0 0 vs hb
        simp only [Option.map_some, packBlock, encV, ne_eq, hth, not_false_eq_true, ite_true,
          Nat.zero_add]
        rw [flatten_fields K defs _ vs (by rw [hlen, ← LayL.length hls]; omega)]
    | @array t' l hl' =>
      simp only [hashField, readV, hashBlock]
      simp only [show (Encoding.Array = Encoding.Static) = False by simp,
        show (Encoding.Array = Encoding.Dynamic) = False by simp, ite_false, ite_true,
        List.length_singleton, ne_eq, not_true_eq_false, and_false, true_and]
      cases wordAt data loc with
      | none => simp
      | some w =>
        simp only
        have hmap := blockLoop_map data (hashField K data fuel) (readV data fuel)
          (fun _ v => encV K defs t' v) [l] true (loc + 32) (wordVal w) 0 0 (by
            intro k _ loc'
            simpa using hashField_spec K defs data fuel loc' hl')
        rw [hmap]
        cases blockLoop data (readV data fuel) [l] true (loc + 32) (wordVal w) 0 0 with
        | none => simp
        | some vs =>
          simp only [Option.map_some, packBlock, encV, ne_eq, not_true_eq_false, ite_false]
          rw [flatten_same K defs t' vs]
    | @fixed t' n l hn hl' =>
      simp only [hashField, readV, hashBlock]
      simp only [show (Encoding.Tuple = Encoding.Static) = False by simp,
        show (Encoding.Tuple = Encoding.Dynamic) = False by simp,
        show (Encoding.Tuple = Encoding.Array) = False by simp, ite_false, ite_true,
        Bool.false_eq_true, false_and]
      have hmap := blockLoop_map data (hashField K data fuel) (readV data fuel)
        (fun _ v => encV K defs t' v) (List.replicate n l) false loc n 0 0 (by
          intro k hk loc'
          simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
          have hg : (List.replicate n l).getD k default = l := by
            simp [List.getD_eq_getElem?_getD, hk]
          rw [hg]
          exact hashField_spec K defs data fuel loc' hl')
      simp only [List.length_replicate]
      rw [hmap]
      cases blockLoop data (readV data fuel) (List.replicate n l) false loc n 0 0 with
      | none => simp
      | some vs =>
        simp only [Option.map_some, packBlock, encV, ne_eq, not_true_eq_false, ite_false]
        rw [flatten_same K defs t' vs]

end EIP712
