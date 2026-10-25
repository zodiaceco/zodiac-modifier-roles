import Bridge.Normalize

/-!
# What normalization leaves alone

`normalize_plain`: plain nodes (type descriptions, leaf checks, `Slice`
windows) are fixed points. `nodes_normalize`: a property of single nodes
(their encoding, operator and compValue) that the fresh nodes normalization
makes (`Or` nodes) satisfy holds of every node of the
normalized tree if it holds of every node of the input (e.g. `CvOk`).
-/

namespace Bridge
open Normalize

/-! ## Plain nodes -/

theorem eraseDups_short {α} [BEq α] : ∀ l : List α, l.length ≤ 1 → l.eraseDups.length ≤ 1
  | [], _ => by simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
  | [_], _ => by simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
  | _ :: _ :: _, h => by simp at h

theorem normalize_plain : ∀ (k : Nat) (c : Cond), Plain c → normalize k c = c
  | 0, _, _ => rfl
  | k + 1, c, hp => by
    rcases hp with ⟨h1, h2, h5, h4, hch⟩
    rw [normalize]
    split
    · rfl
    dsimp only
    have hc1 : ({ c with ch := c.ch.map (normalize k) } : Cond) = c := by
      have : c.ch.map (normalize k) = c.ch := by
        conv => rhs; rw [← List.map_id c.ch]
        exact List.map_congr_left fun x hx => normalize_plain k x (hch x hx)
      rw [this]; cases c; rfl
    rw [hc1]
    have hlog : isLogical c = false := by
      unfold isLogical; simp [h1, h2]
    have hflat : flatten c = c := by unfold flatten; simp [hlog]
    have hded : dedupe c = c := by unfold dedupe; simp [hlog]
    have hunw : unwrap c = c := by unfold unwrap; simp [hlog]
    have hpush : pushDownOr (normalize k) c = c := by
      unfold pushDownOr pushStep; simp [h2]
    have hsort : sortB c = c := by unfold sortB; simp [hlog]
    rw [hflat, hded, hunw, hpush, hsort]

end Bridge
