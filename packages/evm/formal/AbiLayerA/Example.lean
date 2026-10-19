import AbiLayerA.Main

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

namespace AbiLayerA.Example
open AbiLayerA Roles

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
  .call rfl rfl (by simp [args])
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
example := layerA_input root selector args [] root_desc root_ok
  (by decide +kernel) visits_memo rfl

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
  .call rfl rfl (by simp) (.cons (.desc (.word rfl rfl rfl (length_word _))) .nil) (.inl rfl)

/-- `interpA` describes `data`; `interpB` does not fit (and needs `s = true`). -/
theorem root2_desc : Desc true root2 (.call selector args2) :=
  .call rfl rfl (by simp [args2])
    (.cons (.desc (.logical interpA rfl (.inr rfl) (by simp [orNode, node]) (.desc interpA_desc)
        (by
          intro ch hm
          simp [orNode, node] at hm
          rcases hm with rfl | rfl
          · exact .ds (.desc interpA_desc)
          · exact .ds (.stray rfl (.abi rfl) trivial))))
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
example := layerA_input root2 selector args2 [] root2_desc root2_ok
  (by decide +kernel) visits_slice_leaf rfl

/-- On these bytes it is the window case: the compared value is `0x34`, the
    last byte of `x = 0x1234`, a window of `x`'s word. -/
example : input data2 67 leafSliced = .word (wordVal [0x34]) ∧
    IsWindow [0x34] (content xVal) := by
  refine ⟨by decide +kernel, 31, by decide, by decide +kernel⟩

end AbiLayerA.Example
