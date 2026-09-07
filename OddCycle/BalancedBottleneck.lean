import OddCycle.ChangedEvents
import OddCycle.ShortOrientation
import OddCycle.QueueLengthDynamics

/-! The operational bottleneck: in the balanced family an orientation-changing
completion is necessarily the head completion of the queue holding every job. -/

namespace OddCycle

theorem balanced_orientation_change_head {w pos init : Nat} {s t : State} {side : Bool}
    (hw : 2 ≤ w) (hv : Valid (2 * w + 1) s) (hb : balanced w s = true)
    (he : transition (cycleAdjacent (2 * w + 1)) w s side pos = some (t, init))
    (hchange : orientation (2 * w + 1) s ≠ orientation (2 * w + 1) t) :
    pos = 0 ∧ (if side then s.1 = [] else s.2 = []) := by
  apply balanced_changed_event_head hw (show w ≤ 2 * w + 1 by omega) hv hb
  intro hsame
  rw [hsame] at he
  exact hchange (large_budget_preserves_orientation (by omega) hv (by omega) he)

theorem balanced_orientation_change_boundary {w pos init : Nat} {s t : State} {side : Bool}
    (hw : 2 ≤ w) (hv : Valid (2 * w + 1) s) (hb : balanced w s = true)
    (he : transition (cycleAdjacent (2 * w + 1)) w s side pos = some (t, init))
    (hchange : orientation (2 * w + 1) s ≠ orientation (2 * w + 1) t) :
    pos = 0 ∧ (s.1.length = 0 ∨ s.1.length = 2 * w + 1) := by
  have hh := balanced_orientation_change_head hw hv hb he hchange
  have hl := hv.length_eq
  simp only [List.length_append, List.length_range] at hl
  refine ⟨hh.1, ?_⟩
  cases side with
  | false =>
    have hnil : s.2 = [] := hh.2
    simp only [hnil, List.length_nil, Nat.add_zero] at hl
    exact Or.inr hl
  | true =>
    have hnil : s.1 = [] := hh.2
    exact Or.inl (by simp [hnil])

theorem balanced_orientation_change_unique_position {w p q i j : Nat} {s t u : State} {side side' : Bool}
    (hw : 2 ≤ w) (hv : Valid (2 * w + 1) s) (hb : balanced w s = true)
    (ht : transition (cycleAdjacent (2 * w + 1)) w s side p = some (t, i))
    (hu : transition (cycleAdjacent (2 * w + 1)) w s side' q = some (u, j))
    (hct : orientation (2 * w + 1) s ≠ orientation (2 * w + 1) t)
    (hcu : orientation (2 * w + 1) s ≠ orientation (2 * w + 1) u) :
    side = side' ∧ p = q := by
  have h₁ := balanced_orientation_change_head hw hv hb ht hct
  have h₂ := balanced_orientation_change_head hw hv hb hu hcu
  refine ⟨?_, h₁.1.trans h₂.1.symm⟩
  have hl := hv.length_eq
  cases side <;> cases side' <;> try rfl
  all_goals
    simp only [Bool.false_eq_true, if_false, if_true] at h₁ h₂
    simp only [h₁.2, h₂.2, List.length_append, List.length_nil, List.length_range] at hl
    omega

end OddCycle
