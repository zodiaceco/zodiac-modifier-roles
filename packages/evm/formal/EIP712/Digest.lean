import EIP712.Decode

/-!
# The signed digest

`hashTypedMessage_spec`: when the SDK's `types` array rebuilds (`_toTree`)
into the type trees of `EIP712Domain` (node 0) and of the primary type
(node 1), and `domain` / `message` are the spec ABI encodings of typed
values, the contract returns the EIP-712 digest of those values.

`layOf` computes the type tree from the definitions; `layOf_lay` shows it
is one. The driver compares it with `_toTree` of the SDK's `toAbiTypes`
output (`lay` query), which checks the hypothesis on the fuzz corpus.
-/

namespace EIP712
open DecoderFaithfulness DecoderFaithfulness.Roles

theorem At_self (bs : Bytes) : At bs 0 bs := by simp [At]

theorem hashStructE_spec (K : Bytes → Bytes) (defs : Defs) (data : Bytes) (types : List TNF)
    (index : Nat) (s : String) (v : V) (t : TN)
    (hlen : data.length < 2 ^ 255)
    (htree : toTree types (types.length + 1) index = some t)
    (hl : Lay K defs (.struct s) t) (hv : HasTy defs (.struct s) v)
    (hdata : data = enc (abiOf defs (.struct s) v)) :
    hashStructE K data types index = some (hashStruct K defs s v) := by
  unfold hashStructE
  rw [htree]
  simp only
  have hroot : t.encoding = .Tuple ∧ t.typeHash ≠ zeros 32 := by
    cases hl with
    | struct _ _ _ hth => exact ⟨rfl, hth⟩
  rw [if_neg (by rintro (h | h); exact h hroot.1; exact hroot.2 h)]
  rw [hashField_spec K defs data _ 0 hl]
  rw [readV_enc K defs data hlen _ 0 hv hl (Nat.le_refl _) (by rw [hdata]; exact At_self _)]
  rfl

/-- **The contract signs the EIP-712 digest** of the SDK-encoded domain and
    message, provided its type trees are the SDK's (`htree0`, `htree1`). -/
theorem hashTypedMessage_spec (K : Bytes → Bytes) (defs : Defs) (primary : String)
    (types : List TNF) (dv mv : V) (td tm : TN)
    (h0 : toTree types (types.length + 1) 0 = some td) (hl0 : Lay K defs (.struct "EIP712Domain") td)
    (h1 : toTree types (types.length + 1) 1 = some tm) (hl1 : Lay K defs (.struct primary) tm)
    (hdv : HasTy defs (.struct "EIP712Domain") dv) (hmv : HasTy defs (.struct primary) mv)
    (hdl : (enc (abiOf defs (.struct "EIP712Domain") dv)).length < 2 ^ 255)
    (hml : (enc (abiOf defs (.struct primary) mv)).length < 2 ^ 255) :
    hashTypedMessage K (enc (abiOf defs (.struct "EIP712Domain") dv))
      (enc (abiOf defs (.struct primary) mv)) types = some (digest K defs primary dv mv) := by
  unfold hashTypedMessage
  rw [hashStructE_spec K defs _ types 0 "EIP712Domain" dv td hdl h0 hl0 hdv rfl,
    hashStructE_spec K defs _ types 1 primary mv tm hml h1 hl1 hmv rfl]
  simp [digest, List.append_assoc]

/-! ## Computing the type tree -/

/-- The type tree of `ty` (`fuel`: nesting depth; `none` if out of fuel,
    for an undefined or empty struct, or `T[0]`). -/
def layOf (K : Bytes → Bytes) (defs : Defs) : Nat → Ty → Option TN
  | 0, _ => none
  | _ + 1, .atom _ => some ⟨.Static, [], zeros 32⟩
  | _ + 1, .bytes => some ⟨.Dynamic, [], zeros 32⟩
  | _ + 1, .string => some ⟨.Dynamic, [], zeros 32⟩
  | f + 1, .array t => (layOf K defs f t).map fun l => ⟨.Array, [l], zeros 32⟩
  | f + 1, .fixed t n =>
    if n = 0 then none else (layOf K defs f t).map fun l => ⟨.Tuple, List.replicate n l, zeros 32⟩
  | f + 1, .struct s =>
    if defs.lookup s = none ∨ fieldsOf defs s = [] ∨ typeHash K defs s = zeros 32 then none
    else ((fieldsOf defs s).mapM fun fd => layOf K defs f fd.ty).map
      fun ls => ⟨.Tuple, ls, typeHash K defs s⟩

theorem mapM_layL (K : Bytes → Bytes) (defs : Defs) (f : Nat)
    (ih : ∀ ty t, layOf K defs f ty = some t → Lay K defs ty t) :
    ∀ (fs : List Field) (ls : List TN), fs.mapM (fun fd => layOf K defs f fd.ty) = some ls →
      LayL K defs (fs.map (·.ty)) ls
  | [], ls, h => by simp at h; subst h; exact .nil
  | fd :: fs, ls, h => by
    simp only [List.mapM_cons] at h
    cases h1 : layOf K defs f fd.ty with
    | none => rw [h1] at h; simp at h
    | some l =>
      rw [h1] at h
      cases h2 : fs.mapM (fun fd => layOf K defs f fd.ty) with
      | none => rw [h2] at h; simp at h
      | some ls' =>
        rw [h2] at h
        simp at h
        subst h
        exact .cons (ih _ _ h1) (mapM_layL K defs f ih fs ls' h2)

theorem layOf_lay (K : Bytes → Bytes) (defs : Defs) :
    ∀ (fuel : Nat) (ty : Ty) (t : TN), layOf K defs fuel ty = some t → Lay K defs ty t
  | 0, _, _, h => by simp [layOf] at h
  | f + 1, .atom _, t, h => by simp [layOf] at h; subst h; exact .atom
  | f + 1, .bytes, t, h => by simp [layOf] at h; subst h; exact .bytes
  | f + 1, .string, t, h => by simp [layOf] at h; subst h; exact .string
  | f + 1, .array ty, t, h => by
    simp only [layOf] at h
    cases h1 : layOf K defs f ty with
    | none => rw [h1] at h; simp at h
    | some l => rw [h1] at h; simp at h; subst h; exact .array (layOf_lay K defs f ty l h1)
  | f + 1, .fixed ty n, t, h => by
    simp only [layOf] at h
    split at h
    · simp at h
    · cases h1 : layOf K defs f ty with
      | none => rw [h1] at h; simp at h
      | some l =>
        rw [h1] at h; simp at h; subst h
        exact .fixed (by omega) (layOf_lay K defs f ty l h1)
  | f + 1, .struct s, t, h => by
    simp only [layOf] at h
    split at h
    · simp at h
    · rename_i hc
      simp only [not_or] at hc
      obtain ⟨hd, hne, hth⟩ := hc
      cases h1 : (fieldsOf defs s).mapM (fun fd => layOf K defs f fd.ty) with
      | none => rw [h1] at h; simp at h
      | some ls =>
        rw [h1] at h; simp at h; subst h
        have hl := mapM_layL K defs f (layOf_lay K defs f) _ ls h1
        refine .struct hd hl ?_ hth
        intro he; subst he
        have := LayL.length hl
        simp at this
        exact hne this

end EIP712
