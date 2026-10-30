import DecoderFaithfulness.Desc

/-!
# Values found by following offsets

`LP data l u`: reading `data` from `l` the way an ABI decoder does (heads in
place, a dynamic component through its offset word, relative to the start
of its block) yields `u`. Unlike `Placed`, nothing is assumed about the
layout: tails may come in any order, with gaps, shared, or anywhere else in
`data`; padding and unreferenced bytes are arbitrary. This is what a
target contract's decoder sees (`Decoder.lean` shows solc's accepts only
such calldata).

`HasSh u s`: `u` has the shape `s` (its ABI type, up to array lengths).
A value is determined by its location and shape (`LP.det`).
-/

namespace TargetDecode
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- An ABI type up to array lengths. `call n args`: nested calldata with
    `n` leading bytes. -/
inductive Sh where
  | word
  | bytes
  | tuple (cs : List Sh)
  | array (e : Sh)
  | call (n : Nat) (args : List Sh)
  deriving Inhabited

/-- `u` has shape `s`. -/
inductive HasSh : Val → Sh → Prop
  | word {w : Bytes} : w.length = 32 → HasSh (.word w) .word
  | bytes {b : Bytes} : HasSh (.bytes b) .bytes
  | tuple {vs : List Val} {cs : List Sh} : vs.length = cs.length →
      (∀ i (h : i < vs.length) (h' : i < cs.length), HasSh vs[i] cs[i]) →
      HasSh (.tuple vs) (.tuple cs)
  | array {vs : List Val} {e : Sh} : (∀ i (h : i < vs.length), HasSh vs[i] e) →
      HasSh (.array vs) (.array e)
  | call {pre : Bytes} {args : List Val} {n : Nat} {cs : List Sh} : pre.length = n →
      args.length = cs.length →
      (∀ i (h : i < args.length) (h' : i < cs.length), HasSh args[i] cs[i]) →
      HasSh (.call pre args) (.call n cs)

/-- Where component `i` of a block starts within its head: static
    components take their encoding's length, dynamic ones one offset word. -/
def headOff : List Val → Nat → Nat
  | v :: vs, i + 1 => (if v.isStatic then (enc v).length else 32) + headOff vs i
  | _, _ => 0

/-- `u` is what following offsets from `l` in `data` reads. -/
inductive LP : Bytes → Nat → Val → Prop
  | word {data : Bytes} {l : Nat} {w : Bytes} : At data l w → LP data l (.word w)
  | bytes {data : Bytes} {l : Nat} {b : Bytes} : l + 32 ≤ data.length →
      load data l = b.length → At data (l + 32) b → LP data l (.bytes b)
  | tuple {data : Bytes} {l : Nat} {vs : List Val} :
      (∀ i (h : i < vs.length), vs[i].isStatic = true → LP data (l + headOff vs i) vs[i]) →
      (∀ i (h : i < vs.length), vs[i].isStatic = false → l + headOff vs i + 32 ≤ data.length) →
      (∀ i (h : i < vs.length), vs[i].isStatic = false →
        LP data (l + load data (l + headOff vs i)) vs[i]) →
      LP data l (.tuple vs)
  | array {data : Bytes} {l : Nat} {vs : List Val} : l + 32 ≤ data.length →
      load data l = vs.length →
      (∀ i (h : i < vs.length), vs[i].isStatic = true → LP data ((l + 32) + headOff vs i) vs[i]) →
      (∀ i (h : i < vs.length), vs[i].isStatic = false → (l + 32) + headOff vs i + 32 ≤ data.length) →
      (∀ i (h : i < vs.length), vs[i].isStatic = false →
        LP data ((l + 32) + load data ((l + 32) + headOff vs i)) vs[i]) →
      LP data l (.array vs)
  /-- Nested calldata in a `bytes` value: the callee decodes the content
      `c`, starting after the `pre.length` leading bytes. -/
  | call {data : Bytes} {l : Nat} {pre : Bytes} {args : List Val} {c : Bytes} :
      l + 32 ≤ data.length → load data l = c.length → At data (l + 32) c →
      pre.length ≤ c.length → c.take pre.length = pre →
      (∀ i (h : i < args.length), args[i].isStatic = true → LP c (pre.length + headOff args i) args[i]) →
      (∀ i (h : i < args.length), args[i].isStatic = false → pre.length + headOff args i + 32 ≤ c.length) →
      (∀ i (h : i < args.length), args[i].isStatic = false →
        LP c (pre.length + load c (pre.length + headOff args i)) args[i]) →
      LP data l (.call pre args)

/-- The calldata of a call `pre ++ args`, as the callee decodes it. -/
def LPCall (data pre : Bytes) (args : List Val) : Prop :=
  pre.length ≤ data.length ∧ data.take pre.length = pre ∧
  (∀ i (h : i < args.length), args[i].isStatic = true →
    LP data (pre.length + headOff args i) args[i]) ∧
  (∀ i (h : i < args.length), args[i].isStatic = false →
    pre.length + headOff args i + 32 ≤ data.length ∧
    LP data (pre.length + load data (pre.length + headOff args i)) args[i])

/-! ## Shapes fix static-ness and static sizes -/

mutual
  def Sh.isStatic : Sh → Bool
    | .word => true
    | .tuple cs => Sh.allStatic cs
    | _ => false
  def Sh.allStatic : List Sh → Bool
    | [] => true
    | c :: cs => c.isStatic && Sh.allStatic cs
end

mutual
  /-- The encoded size of a static value of this shape. -/
  def Sh.size : Sh → Nat
    | .word => 32
    | .tuple cs => Sh.sizeAll cs
    | _ => 0
  def Sh.sizeAll : List Sh → Nat
    | [] => 0
    | c :: cs => c.size + Sh.sizeAll cs
end

theorem allStatic_iff : ∀ (vs : List Val), Val.allStatic vs = true ↔
    ∀ i (h : i < vs.length), vs[i].isStatic = true
  | [] => by simp [Val.allStatic]
  | v :: vs => by
    simp only [Val.allStatic, Bool.and_eq_true, allStatic_iff vs]
    constructor
    · rintro ⟨h0, hr⟩ i hi
      cases i with
      | zero => exact h0
      | succ i => exact hr i (by simp at hi; omega)
    · intro h
      exact ⟨h 0 (by simp), fun i hi => h (i + 1) (by simp; omega)⟩

theorem shAllStatic_iff : ∀ (cs : List Sh), Sh.allStatic cs = true ↔
    ∀ i (h : i < cs.length), cs[i].isStatic = true
  | [] => by simp [Sh.allStatic]
  | c :: cs => by
    simp only [Sh.allStatic, Bool.and_eq_true, shAllStatic_iff cs]
    constructor
    · rintro ⟨h0, hr⟩ i hi
      cases i with
      | zero => exact h0
      | succ i => exact hr i (by simp at hi; omega)
    · intro h
      exact ⟨h 0 (by simp), fun i hi => h (i + 1) (by simp; omega)⟩

theorem HasSh.isStatic {u : Val} {s : Sh} (h : HasSh u s) : u.isStatic = s.isStatic := by
  induction h with
  | word => rfl
  | bytes => rfl
  | @tuple vs cs hl _ ih =>
    simp only [Val.isStatic, Sh.isStatic]
    rw [Bool.eq_iff_iff, allStatic_iff, shAllStatic_iff]
    constructor
    · intro h i hi
      rw [← ih i (by omega) hi]; exact h i (by omega)
    · intro h i hi
      rw [ih i hi (by omega)]; exact h i (by omega)
  | array => rfl
  | call => rfl

/-! ## Determinism -/

theorem At.unique {data x y : Bytes} {l : Nat} (hx : At data l x) (hy : At data l y)
    (hl : x.length = y.length) : x = y := by
  rw [← hx.1, ← hy.1, hl]

theorem encParts_static : ∀ (vs : List Val) (off : Nat), Val.allStatic vs = true →
    (encParts vs off).2 = [] ∧ (encParts vs off).1.length = headLen vs
  | [], _, _ => by simp [encParts, headLen]
  | v :: vs, off, h => by
    simp only [Val.allStatic, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := encParts_static vs off h.2
    simp [encParts, headLen, h.1, h1, h2]

theorem headLen_sizeAll : ∀ (vs : List Val) (cs : List Sh), vs.length = cs.length →
    (∀ i (h : i < vs.length) (h' : i < cs.length),
      vs[i].isStatic = true → (enc vs[i]).length = cs[i].size) →
    Val.allStatic vs = true → headLen vs = Sh.sizeAll cs
  | [], [], _, _, _ => by simp [headLen, Sh.sizeAll]
  | v :: vs, c :: cs, hl, h, hs => by
    simp only [Val.allStatic, Bool.and_eq_true] at hs
    simp only [headLen, Sh.sizeAll, hs.1, ite_true]
    have h0 := h 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [h0 hs.1, headLen_sizeAll vs cs (by simpa using hl)
        (fun i hi hi' => h (i + 1) (by simp; omega) (by simp; omega)) hs.2]
  | [], _ :: _, hl, _, _ | _ :: _, [], hl, _, _ => by simp at hl

/-- The encoding of a static value has its shape's size. -/
theorem HasSh.size {u : Val} {s : Sh} (h : HasSh u s) : u.isStatic = true →
    (enc u).length = s.size := by
  induction h with
  | word hw => intro _; simpa [enc, Sh.size] using hw
  | bytes => intro h; simp [Val.isStatic] at h
  | @tuple vs cs hl _ ih =>
    intro hst
    simp only [Val.isStatic] at hst
    rw [enc_tuple, encTuple, List.length_append, (encParts_static vs _ hst).1,
      (encParts_static vs _ hst).2, List.length_nil, Nat.add_zero, Sh.size]
    exact headLen_sizeAll vs cs hl (fun i hi hi' hs => ih i hi hi' hs) hst
  | array => intro h; simp [Val.isStatic] at h
  | call => intro h; simp [Val.isStatic] at h

/-- Components of the same shapes sit at the same head offsets. -/
theorem headOff_eq : ∀ (vs ws : List Val) (i : Nat),
    (∀ j (h : j < vs.length) (h' : j < ws.length), vs[j].isStatic = ws[j].isStatic ∧
      (vs[j].isStatic = true → (enc vs[j]).length = (enc ws[j]).length)) →
    vs.length = ws.length → headOff vs i = headOff ws i
  | v :: vs, w :: ws, i + 1, h, hl => by
    simp only [headOff]
    obtain ⟨h1, h2⟩ := h 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h1 h2
    rw [headOff_eq vs ws i (fun j hj hj' => h (j + 1) (by simp; omega) (by simp; omega))
      (by simpa using hl), h1]
    split
    · rename_i hs; rw [h2 (h1 ▸ hs)]
    · rfl
  | [], [], _, _, _ => rfl
  | _ :: _, _ :: _, 0, _, _ => rfl
  | [], _ :: _, _, _, hl | _ :: _, [], _, _, hl => by simp at hl

theorem getD_get (cs : List Sh) {j : Nat} (h : j < cs.length) : cs.getD j default = cs[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- Pointwise shapes give the hypotheses of `headOff_eq`. -/
theorem sameSlots {vs ws : List Val} {sh : Nat → Sh}
    (hv : ∀ j (h : j < vs.length), HasSh vs[j] (sh j))
    (hw : ∀ j (h : j < ws.length), HasSh ws[j] (sh j)) :
    ∀ j (h : j < vs.length) (h' : j < ws.length), vs[j].isStatic = ws[j].isStatic ∧
      (vs[j].isStatic = true → (enc vs[j]).length = (enc ws[j]).length) := by
  intro j h h'
  have e1 := (hv j h).isStatic
  have e2 := (hw j h').isStatic
  refine ⟨by rw [e1, e2], fun hs => ?_⟩
  rw [(hv j h).size hs, (hw j h').size (by rw [e2, ← e1]; exact hs)]

/-- **A value is determined by its location and shape.** -/
theorem LP.det {data : Bytes} {l : Nat} {u : Val} (h : LP data l u) :
    ∀ {v : Val} {s : Sh}, LP data l v → HasSh u s → HasSh v s → u = v := by
  induction h with
  | @word data l w hat =>
    intro v s hv hu hs
    cases hu with
    | word hw =>
      cases hs with
      | word hw' =>
        cases hv with
        | word hat' => rw [At.unique hat hat' (by rw [hw, hw'])]
  | @bytes data l b _ hlen hat =>
    intro v s hv hu hs
    cases hu
    cases hs
    cases hv with
    | bytes _ hlen' hat' => rw [At.unique hat hat' (by omega)]
  | @tuple data l vs _ _ _ ihs ihd =>
    intro v s hv hu hs
    cases hu with
    | @tuple _ cs hl hsh =>
      cases hs with
      | @tuple ws _ hl' hsh' =>
        cases hv with
        | tuple hs1 _ hd1 =>
          have hlen : vs.length = ws.length := by omega
          have hpt := sameSlots (sh := fun j => cs.getD j default)
            (fun j hj => by
              have := hsh j hj (by omega); rwa [getD_get cs (by omega)])
            (fun j hj => by
              have := hsh' j hj (by omega); rwa [getD_get cs (by omega)])
          congr 1
          apply List.ext_getElem hlen
          intro i hi hi'
          have hoff := headOff_eq vs ws i hpt hlen
          have hsi : HasSh vs[i] cs[i] := hsh i hi (by omega)
          have hsi' : HasSh ws[i] cs[i] := hsh' i hi' (by omega)
          cases hst : vs[i].isStatic
          · have hst' : ws[i].isStatic = false := by rw [← (hpt i hi hi').1]; exact hst
            have := hd1 i hi' hst'
            rw [← hoff] at this
            exact ihd i hi hst this hsi hsi'
          · have hst' : ws[i].isStatic = true := by rw [← (hpt i hi hi').1]; exact hst
            have := hs1 i hi' hst'
            rw [← hoff] at this
            exact ihs i hi hst this hsi hsi'
  | @array data l vs _ hcount _ _ _ ihs ihd =>
    intro v s hv hu hs
    cases hu with
    | @array _ e hsh =>
      cases hs with
      | @array ws _ hsh' =>
        cases hv with
        | array _ hcount' hs1 _ hd1 =>
          have hlen : vs.length = ws.length := by omega
          have hpt := sameSlots (sh := fun _ => e) hsh hsh'
          congr 1
          apply List.ext_getElem hlen
          intro i hi hi'
          have hoff := headOff_eq vs ws i hpt hlen
          cases hst : vs[i].isStatic
          · have hst' : ws[i].isStatic = false := by rw [← (hpt i hi hi').1]; exact hst
            have := hd1 i hi' hst'
            rw [← hoff] at this
            exact ihd i hi hst this (hsh i hi) (hsh' i hi')
          · have hst' : ws[i].isStatic = true := by rw [← (hpt i hi hi').1]; exact hst
            have := hs1 i hi' hst'
            rw [← hoff] at this
            exact ihs i hi hst this (hsh i hi) (hsh' i hi')
  | @call data l pre args c _ hclen hat hpl htake _ _ _ ihs ihd =>
    intro v s hv hu hs
    cases hu with
    | @call _ _ n cs hn hl hsh =>
      cases hs with
      | @call pre' ws _ _ hn' hl' hsh' =>
        cases hv with
        | @call _ _ _ _ c' _ hclen' hat' hpl' htake' hs1 _ hd1 =>
          have hc : c = c' := At.unique hat hat' (by omega)
          subst hc
          have hpre : pre = pre' := by rw [← htake, ← htake', hn, hn']
          subst hpre
          have hlen : args.length = ws.length := by omega
          have hpt := sameSlots (sh := fun j => cs.getD j default)
            (fun j hj => by
              have := hsh j hj (by omega); rwa [getD_get cs (by omega)])
            (fun j hj => by
              have := hsh' j hj (by omega); rwa [getD_get cs (by omega)])
          congr 1
          apply List.ext_getElem hlen
          intro i hi hi'
          have hoff := headOff_eq args ws i hpt hlen
          have hsi : HasSh args[i] cs[i] := hsh i hi (by omega)
          have hsi' : HasSh ws[i] cs[i] := hsh' i hi' (by omega)
          cases hst : args[i].isStatic
          · have hst' : ws[i].isStatic = false := by rw [← (hpt i hi hi').1]; exact hst
            have := hd1 i hi' hst'
            rw [← hoff] at this
            exact ihd i hi hst this hsi hsi'
          · have hst' : ws[i].isStatic = true := by rw [← (hpt i hi hi').1]; exact hst
            have := hs1 i hi' hst'
            rw [← hoff] at this
            exact ihs i hi hst this hsi hsi'

end TargetDecode
