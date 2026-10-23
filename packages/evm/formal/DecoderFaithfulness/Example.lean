import DecoderFaithfulness.Main

/-!
# Examples: the theorems apply to real condition trees

1. `f(uint256 amount, bytes memo)` scoped with `EqualTo` on both arguments,
   with every interpretation holding (`s = false`).
2. `f(bytes data, uint256 x)` where `data` is checked under two nested-calldata
   interpretations (a variant `Or`; the calldata fits only the first) and the
   last byte of `x` is checked with a `Slice` (`s = true`).

They show that the hypotheses are satisfiable, and what the conclusions say
on concrete bytes.
-/

namespace DecoderFaithfulness.Example
open DecoderFaithfulness Roles

def node (e : Encoding) (o : Operator) (cs : List Condition) (lb : Nat := 0)
    (cv : Bytes := []) : Condition :=
  ⟨e, o, cs, false, 0, lb, cv⟩

theorem input_ne_ether {data : Bytes} {l : Nat} {c : Condition} (h : c.encoding ≠ .None) :
    input data l c ≠ .etherValue := by
  unfold input; rw [ite_eq_right h]; dsimp only
  repeat (first | split | simp)

/-! ## 1. `f(uint256 amount, bytes memo)` -/

def root : Condition :=
  node .AbiEncoded .Matches [node .Static .EqualTo [], node .Dynamic .EqualTo []] 4

def selector : Bytes := natBE 4 0xa9059cbb
def memo : Bytes := [0x68, 0x69]  -- "hi"
def args : List Val := [.word (word 1000), .bytes memo]

theorem root_desc : Desc false root (.call selector args) :=
  .call rfl rfl (by simp [root, node]) (by simp [root, node, args])
    (.cons (.desc (.word rfl rfl rfl (length_word _)))
      (.cons (.desc (.bytes rfl rfl rfl trivial)) .nil)) (.inl rfl)

theorem root_ok : RootOK root := .abi rfl

/-- What the evaluator sees after pack/unpack: `amount` inlined (32 bytes),
    `memo` not inlined. -/
def packed : Condition :=
  ⟨.AbiEncoded, .Matches, [⟨.Static, .EqualTo, [], true, 32, 0, []⟩,
    ⟨.Dynamic, .EqualTo, [], false, 0, 0, []⟩], false, 0, 4, []⟩

theorem annotate_root : annotate root = packed := by
  simp [root, packed, node, annotate_eq, isInlined_eq, inlinedSize_eq, isInlinedAll]

def data : Bytes := calldata selector args []

set_option maxRecDepth 100000 in
/-- `children` places `amount` at byte 4 and `memo`'s tail at byte 68. -/
theorem children_root : children data 4 packed = some [4, 68] := by decide +kernel

/-- The evaluator reaches the `memo` condition (child 1 of `Matches`) at 68. -/
theorem visits_memo :
    Visit data (annotate root) 0 [1] ⟨.Dynamic, .EqualTo, [], false, 0, 0, []⟩ 68 := by
  rw [annotate_root]
  exact .matchesChild [4, 68] 1 (by decide) rfl children_root rfl .here

/-- The theorem applies: for `memo`, `__input` yields exactly the spec
    encoding of the described component, the window case, the ether value,
    or nothing (strict mode rules the last one out). -/
example := decoder_input root selector args [] root_desc root_ok (.of_noZip rfl)
  (by decide +kernel) (.visit visits_memo) rfl

/-- On these bytes it is the first case: the full spec encoding of `memo`
    (length word + "hi" + padding), which `EqualTo` keccak-hashes. -/
example : input data 68 ⟨.Dynamic, .EqualTo, [], false, 0, 0, []⟩ =
    expectInput (enc (.bytes memo)) := by decide +kernel

/-! ## 2. Variant `Or` and `Slice`: `f(bytes data, uint256 x)` -/

/-- `data` is either `g(uint256)` or `h(uint256, uint256)` calldata. -/
def interpA : Condition := node .AbiEncoded .Matches [node .Static .Pass []] 4
def interpB : Condition :=
  node .AbiEncoded .Matches [node .Static .Pass [], node .Static .Pass []] 4
def orNode : Condition := node .None .Or [interpA, interpB]

/-- The last byte of `x` (`shift = 31`, `size = 1`). -/
def sliceNode : Condition :=
  node .Static .Slice [node .Static .EqualTo []] 0 [0, 31, 1]

def root2 : Condition := node .AbiEncoded .Matches [orNode, sliceNode] 4

def dataVal : Val := .call (natBE 4 0x11111111) [.word (word 7)]
def xVal : Val := .word (word 0x1234)
def args2 : List Val := [dataVal, xVal]

theorem interpA_desc : Desc true interpA dataVal :=
  .call rfl rfl (by simp [interpA, node]) (by simp [interpA, node, dataVal])
    (.cons (.desc (.word rfl rfl rfl (length_word _))) .nil) (.inl rfl)

/-- `interpA` describes `data`; `interpB` does not fit (and needs `s = true`). -/
theorem root2_desc : Desc true root2 (.call selector args2) :=
  .call rfl rfl (by simp [root2, node]) (by simp [root2, node, args2])
    (.cons (.desc (.logical interpA rfl (.inr rfl) (by simp [orNode, node]) (.desc interpA_desc)
        (by
          intro ch hm
          simp [orNode, node] at hm
          rcases hm with rfl | rfl
          · exact .ds (.desc interpA_desc)
          · exact .ds (.stray rfl (.abi rfl) trivial))
        ⟨[], [interpB], rfl, by simp⟩))
      (.cons (.desc (.sliceWord rfl rfl rfl (by decide) (by decide) (.leaf rfl rfl rfl)
        (length_word _))) .nil)) (.inl rfl)

theorem root2_ok : RootOK root2 := .abi rfl

def data2 : Bytes := calldata selector args2 []

/-- The slice's child after pack/unpack, with `size` overridden to 1. -/
def leafSliced : Condition := ⟨.Static, .EqualTo, [], true, 1, 0, []⟩

theorem annotate_root2_child1 :
    (annotate root2).children.getD 1 default = ⟨.Static, .Slice,
      [⟨.Static, .EqualTo, [], true, 32, 0, []⟩], true, 32, 0, [0, 31, 1]⟩ := by
  simp [root2, sliceNode, node, annotate_eq, isInlined_eq, inlinedSize_eq, isInlinedAll]

set_option maxRecDepth 100000 in
theorem children_root2 : children data2 4 (annotate root2) = some [68, 36] := by
  have : annotate root2 = ⟨.AbiEncoded, .Matches, [annotate orNode, ⟨.Static, .Slice,
      [⟨.Static, .EqualTo, [], true, 32, 0, []⟩], true, 32, 0, [0, 31, 1]⟩], false, 0, 4, []⟩ := by
    rw [annotate_eq]
    simp [root2, sliceNode, node, annotate_eq, isInlined_eq, inlinedSize_eq, isInlinedAll]
  have hor : (annotate orNode).inlined = false ∧ (annotate orNode).size = 0 := by
    simp [orNode, interpA, interpB, node, annotate_eq, isInlined_eq, isInlinedAll]
  rw [this]
  unfold children
  simp only [reduceCtorEq, ite_false, List.length_cons, List.length_nil]
  simp only [childrenLoop, List.getD_cons_zero, List.getD_cons_succ, hor]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The evaluator reaches the slice's child at byte 67 (the last byte of `x`). -/
theorem visits_slice_leaf : Visit data2 (annotate root2) 0 [1] leafSliced 67 := by
  apply Visit.matchesChild [68, 36] 1 (by decide) (by rw [annotate_eq]; simp [root2, node])
    (by
      have hlb : (annotate root2).leadingBytes = 4 := by rw [annotate_eq]; simp [root2, node]
      simpa [hlb] using children_root2) (by rw [annotate_eq]; simp [root2, node])
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  rw [annotate_root2_child1]
  exact .slice rfl (by intro h; cases h) (by decide) .here

/-- The theorem applies to the slice's child (`s = true`: `interpB` need
    not hold). -/
example := decoder_input root2 selector args2 [] root2_desc root2_ok (.of_noZip rfl)
  (by decide +kernel) (.visit visits_slice_leaf) rfl

/-- On these bytes it is the window case: the compared value is `0x34`, the
    last byte of `x = 0x1234`, a window of `x`'s word. -/
example : input data2 67 leafSliced = .word (wordVal [0x34]) ∧
    IsWindow [0x34] (content xVal) := by
  refine ⟨by decide +kernel, 31, by decide, by decide +kernel⟩

/-! ## 3. Zip: `f(uint256[] a, uint256[] b)`

`And[Matches[Pluck#0 a, Pluck#1 b], ZipEvery(0, 1)[(EqualTo, Pass)]]`, the
shape Roles' own Zip tests use: pair up `a[i]` and `b[i]`, require
`a[i] == x` for every `i`. All hypotheses hold, including `ZipOK`. -/

mutual
  /-- Every node of a tree, the tree first. -/
  def nodes : Condition → List Condition
    | c@⟨_, _, cs, _, _, _, _⟩ => c :: nodesAll cs
  def nodesAll : List Condition → List Condition
    | [] => []
    | c :: cs => nodes c ++ nodesAll cs
end

theorem nodesAll_mem {ch : Condition} : ∀ {cs : List Condition}, ch ∈ cs →
    ∀ {z}, z ∈ nodes ch → z ∈ nodesAll cs
  | _ :: _, .head _, _, hz => by simp [nodesAll, hz]
  | _ :: _, .tail _ hm, _, hz => by simp [nodesAll, nodesAll_mem hm hz]

theorem nodes_self (c : Condition) : c ∈ nodes c := by
  cases c; simp [nodes]

theorem nodes_child {c ch z : Condition} (hm : ch ∈ c.children) (hz : z ∈ nodes ch) :
    z ∈ nodes c := by
  cases c with
  | mk e o cs i sz lb cv => simp only [nodes, List.mem_cons]; exact .inr (nodesAll_mem hm hz)

theorem mem_nodes {z c : Condition} (h : Sub z c) : z ∈ nodes c := by
  induction h with
  | refl => exact nodes_self _
  | child hm _ ih => exact nodes_child hm ih

theorem Desc.array_elems {s : Bool} {c : Condition} {vs : List Val} (hD : Desc s c (.array vs))
    (he : c.encoding = .Array) : ∃ c0 cs, c.children = c0 :: cs ∧ ∀ v, v ∈ vs → DescS s c0 v := by
  cases hD with
  | array c0 cs _ hch h0 _ _ _ => exact ⟨c0, cs, hch, h0⟩
  | bytes _ _ _ hu | sliceBytes _ _ _ _ _ _ hu => cases hu
  | logical _ h _ _ _ _ _ => rw [he] at h; cases h

/-- A described static leaf is a 32-byte word. -/
theorem DescS.staticLeaf {s : Bool} {c : Condition} {v : Val} (h : DescS s c v)
    (he : c.encoding = .Static) (hch : c.children = []) : ∃ w, v = .word w ∧ w.length = 32 := by
  cases h with
  | desc d =>
    cases d with
    | word _ _ _ hw => exact ⟨_, rfl, hw⟩
    | sliceWord _ _ h _ _ _ _ => rw [hch] at h; cases h
    | bytes h _ _ _ | sliceBytes h _ _ _ _ _ _ | tuple h _ _ _ | array _ _ h _ _ _ _ _
    | call h _ _ _ _ | logical _ h _ _ _ _ _ => rw [he] at h; cases h
  | stray _ hb _ =>
    cases hb with
    | dyn h | abi h | logical _ h _ _ _ _ => rw [he] at h; cases h

def pluckA : Condition := node .Array .Pluck [node .Static .Pass []] 0 [0]
def pluckB : Condition := node .Array .Pluck [node .Static .Pass []] 0 [1]
def args3Node : Condition := node .AbiEncoded .Matches [pluckA, pluckB] 4
def zipTuple : Condition := node .Tuple .Matches [node .Static .EqualTo [], node .Static .Pass []]
def zipNode : Condition := node .None .ZipEvery [zipTuple] 0 [0, 1]
def root3 : Condition := node .None .And [args3Node, zipNode]

def args3 : List Val := [.array [.word (word 1), .word (word 2)], .array [.word (word 3), .word (word 4)]]

theorem pluck_desc {s : Bool} (pk : Condition) (hpk : pk = pluckA ∨ pk = pluckB)
    (vs : List Val) (hvs : ∀ v, v ∈ vs → ∃ w, v = .word w ∧ w.length = 32) :
    Desc s pk (.array vs) := by
  have leaf : ∀ v, v ∈ vs → DescS s (node .Static .Pass []) v := by
    intro v hv
    obtain ⟨w, rfl, hw⟩ := hvs v hv
    exact .desc (.word rfl rfl rfl hw)
  rcases hpk with rfl | rfl <;>
  · refine .array (node .Static .Pass []) [] rfl rfl leaf ?_ ?_ (.inl ⟨rfl, rfl⟩)
    · intro i hi hv
      have : i = 0 := by simp [pluckA, pluckB, node] at hi; omega
      subst this
      exact leaf _ (List.getElem_mem hv)
    · intro j hj hk
      have : j = 0 := by simp [pluckA, pluckB, node] at hj; omega
      subst this
      exact leaf _ (List.getElem_mem _)

theorem root3_desc {s : Bool} : Desc s root3 (.call selector args3) := by
  have hargs : Desc s args3Node (.call selector args3) := by
    refine .call rfl rfl (by simp [args3Node, node]) (by simp [args3Node, node, args3]) ?_ (.inl rfl)
    refine .cons (.desc (pluck_desc _ (.inl rfl) _ ?_)) (.cons (.desc (pluck_desc _ (.inr rfl) _ ?_)) .nil)
    all_goals
      intro v hv
      simp at hv
      rcases hv with rfl | rfl <;> exact ⟨_, rfl, length_word _⟩
  refine .logical args3Node rfl (.inl rfl) (by simp [root3, node]) (.desc hargs) ?_
    ⟨[], [zipNode], rfl, by simp⟩
  intro ch hm
  simp [root3, node] at hm
  rcases hm with rfl | rfl
  · exact .ds (.desc hargs)
  · exact .zip ⟨zipTuple, rfl, .inr rfl, rfl⟩ rfl

theorem root3_ok : RootOK root3 :=
  .logical rfl (.inl rfl) (by
    intro ch hm
    simp [root3, node] at hm
    rcases hm with rfl | rfl
    · exact .ok (.abi rfl)
    · exact .zip ⟨zipTuple, rfl, .inr rfl, rfl⟩)

/-- Integrity's Zip rules, as `ZipOK`: both Plucks the Zip references are
    arrays of words, and both Zip fields describe any word. -/
theorem root3_zipOK {s : Bool} : ZipOK s root3 := by
  intro z pk f hz hpk hzop hf hpkop hidx
  have hz' := mem_nodes hz
  have hpk' := mem_nodes hpk
  simp only [root3, args3Node, pluckA, pluckB, zipNode, zipTuple, node, nodes, nodesAll,
    List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hz' hpk'
  -- The only Zip is `zipNode`; the only Plucks are `pluckA`, `pluckB`.
  rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try (rcases hzop with h | h <;> cases h)) <;>
  rcases hpk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try cases hpkop) <;>
  · refine ⟨rfl, fun vs hD v hv => ?_⟩
    have hf2 : f < 2 := by simpa [zipFields] using hf
    obtain ⟨w, rfl, hw⟩ : ∃ w, v = .word w ∧ w.length = 32 := by
      obtain ⟨c0, cs, hch, h0⟩ := Desc.array_elems hD rfl
      simp only [List.cons.injEq] at hch
      exact DescS.staticLeaf (h0 v hv) (by rw [← hch.1]) (by rw [← hch.1])
    have : f = 0 ∨ f = 1 := by omega
    rcases this with rfl | rfl <;> exact .desc (.word rfl rfl rfl hw)

/-- The theorems apply: every node `evaluate` reaches in `root3`, through
    the Zip as well, is where the spec puts its component. -/
example (p : List Nat) (d : Condition) (l : Nat)
    (hv : Eval (calldata selector args3 []) (annotate root3) p d l) :
    Reached false (calldata selector args3 []) root3 (.call selector args3) p d l :=
  decoder_locations root3 selector args3 [] root3_desc root3_ok root3_zipOK (by decide +kernel) hv

end DecoderFaithfulness.Example
