import OddCycle.UnitGainedPredecessors
import OddCycle.QueueBlocks

/-! The explicit target placement, with an arbitrary ordering of its
interior interval. -/

namespace OddCycle

def unitPlacement (n w : Nat) (H : Queue) : Queue :=
  List.range' 0 (w + 1) ++ ((List.range' (w + 1) (w + 1)).reverse ++ (H ++ (unitInitialBlock n w).reverse))

theorem unitPatternTarget_placement (n w : Nat) (H : Queue) :
    placement (unitPatternTarget n w H.reverse) = unitPlacement n w H := by
  simp [unitPatternTarget, placement, unitTargetTail, unitPlacement, List.range'_succ, List.append_assoc]

theorem unitPlacement_perm {n w : Nat} (hn : 3 * w + 2 ≤ n) {H : Queue}
    (hH : H.Perm (List.range' (2 * w + 2) (n - (3 * w + 2)))) :
    (unitPlacement n w H).Perm (List.range n) := by
  have hp := (List.Perm.refl (List.range' 0 (w + 1))).append
    ((List.reverse_perm (List.range' (w + 1) (w + 1))).append
      (hH.append (List.reverse_perm (unitInitialBlock n w))))
  have h1 : List.range' 0 (w + 1) ++ List.range' (w + 1) (w + 1) = List.range' 0 (2 * w + 2) := by
    simpa only [Nat.zero_add, show (w + 1) + (w + 1) = 2 * w + 2 by omega] using
      (List.range'_append_1 (s := 0) (m := w + 1) (n := w + 1))
  have h2 : List.range' 0 (2 * w + 2) ++ List.range' (2 * w + 2) (n - (3 * w + 2)) =
      List.range' 0 (n - w) := by
    simpa only [Nat.zero_add, show (2 * w + 2) + (n - (3 * w + 2)) = n - w by omega] using
      (List.range'_append_1 (s := 0) (m := 2 * w + 2) (n := n - (3 * w + 2)))
  have h3 : List.range' 0 (n - w) ++ List.range' (n - w) w = List.range n := by
    simpa only [Nat.zero_add, show n - w + w = n by omega, ← List.range_eq_range'] using
      (List.range'_append_1 (s := 0) (m := n - w) (n := w))
  have he : List.range' 0 (w + 1) ++ (List.range' (w + 1) (w + 1) ++
      (List.range' (2 * w + 2) (n - (3 * w + 2)) ++ unitInitialBlock n w)) = List.range n := by
    simp only [← List.append_assoc, h1, h2, unitInitialBlock, h3]
  exact hp.trans (List.Perm.of_eq he)

theorem unitPatternTarget_valid {n w : Nat} (hn : 3 * w + 2 ≤ n) {H : Queue}
    (hH : H.Perm (List.range' (2 * w + 2) (n - (3 * w + 2)))) :
    Valid n (unitPatternTarget n w H.reverse) := by
  have hp := unitPlacement_perm hn hH
  rw [← unitPatternTarget_placement] at hp
  exact ((List.reverse_perm (unitPatternTarget n w H.reverse).2).append_left
    (unitPatternTarget n w H.reverse).1).symm.trans hp

theorem unitPlacement_middle_mem {n w : Nat} (hn : 3 * w + 2 ≤ n) {H : Queue}
    (hH : H.Perm (List.range' (2 * w + 2) (n - (3 * w + 2)))) (x : Nat) :
    x ∈ H ↔ 2 * w + 2 ≤ x ∧ x < n - w := by
  rw [hH.mem_iff, mem_range_interval]
  have he : 2 * w + 2 + (n - (3 * w + 2)) = n - w := by omega
  rw [he]

theorem unitPattern_prefix_labels {n w : Nat} (hw : 1 ≤ w) (hn : 3 * w + 2 ≤ n) {H : Queue}
    (hH : H.Perm (List.range' (2 * w + 2) (n - (3 * w + 2)))) :
    ∀ x ∈ unitInitialBlock n w ++ H.reverse, 2 * w + 2 ≤ x ∧ x < n := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · have hh := mem_range_interval.mp hx
    change n - w ≤ x ∧ x < n - w + w at hh
    omega
  · have hh := (unitPlacement_middle_mem hn hH x).mp (List.mem_reverse.mp hx)
    omega

end OddCycle
