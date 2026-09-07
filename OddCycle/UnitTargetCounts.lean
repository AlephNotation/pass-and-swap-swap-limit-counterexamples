import OddCycle.ReverseCount
import OddCycle.CycleCoordinates

/-! The target's reversed scan has `w+1` replacements exactly at the
insertion positions before its first block boundary. -/

namespace OddCycle

def unitTargetTail (w : Nat) : Queue :=
  List.range' (w + 1) (w + 1) ++ (List.range' 1 w).reverse

theorem unitTargetTail_split (w : Nat) :
    unitTargetTail w = (w + 1) :: (List.range' (w + 2) w ++ (List.range' 1 w).reverse) := by
  simp [unitTargetTail, List.range'_succ]

theorem cycle_consecutive {n i : Nat} (hi : i + 1 < n) : cycleAdjacent n i (i + 1) = true := by
  simp [cycleAdjacent, Nat.mod_eq_of_lt hi]

theorem cycle_far_right {n w x : Nat} (hw : 0 < w) (hx : w + 2 ≤ x) (hxn : x < n) :
    cycleAdjacent n w x = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh := (cycleAdjacent_iff (a := w) (by omega) hxn).mp h
  omega

theorem unit_middle_no_adj {n w : Nat} (hw : 0 < w) (hn : 2 * w + 1 < n) :
    ∀ x ∈ (List.range' (w + 2) w).reverse, cycleAdjacent n w x = false := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp (List.mem_reverse.mp hx)
  exact cycle_far_right hw (by omega) (by omega)

theorem unitTargetTail_backward {n w : Nat} (hw : 0 < w) (hn : 2 * w + 1 < n) :
    replacementCount (cycleAdjacent n) 0 (unitTargetTail w).reverse = w + 1 ∧
      (unlimitedCarry (cycleAdjacent n) 0 (unitTargetTail w).reverse).2 = w + 1 := by
  have hedges : ∀ i, 0 ≤ i → i < 0 + w → cycleAdjacent n i (i + 1) = true := by
    intro i _ hi
    exact cycle_consecutive (by omega)
  have hc := replacementCount_chain (adj := cycleAdjacent n) id 0 w
    ((List.range' (w + 2) w).reverse ++ [w + 1]) hedges
  have hu := unlimitedCarry_chain (adj := cycleAdjacent n) id 0 w hedges
  have hmid := unit_middle_no_adj hw hn
  have ha := cycle_consecutive (n := n) (i := w) (by omega)
  have hrev : (unitTargetTail w).reverse =
      List.range' 1 w ++ ((List.range' (w + 2) w).reverse ++ [w + 1]) := by
    rw [unitTargetTail_split]
    simp [List.reverse_append, List.append_assoc]
  simp only [id_eq, Nat.zero_add, List.map_id] at hc hu
  rw [hrev]
  constructor
  · rw [hc, replacementCount_append, replacementCount_no_adj w _ hmid,
      unlimitedCarry_no_adj w _ hmid]
    simp [replacementCount, ha]
  · rw [unlimitedCarry_append, hu, unlimitedCarry_append, unlimitedCarry_no_adj w _ hmid]
    simp [unlimitedCarry, ha]

theorem unitTargetTail_drop_backward {n w : Nat} (hw : 0 < w) (hn : 2 * w + 1 < n) :
    replacementCount (cycleAdjacent n) 0 ((unitTargetTail w).drop 1).reverse = w := by
  have hedges : ∀ i, 0 ≤ i → i < 0 + w → cycleAdjacent n i (i + 1) = true := by
    intro i _ hi
    exact cycle_consecutive (by omega)
  have hc := replacementCount_chain (adj := cycleAdjacent n) id 0 w (List.range' (w + 2) w).reverse hedges
  simp only [id_eq, Nat.zero_add, List.map_id] at hc
  rw [unitTargetTail_split]
  simp only [List.drop_succ_cons, List.drop_zero, List.reverse_append, List.reverse_reverse]
  rw [hc, replacementCount_no_adj w _ (unit_middle_no_adj hw hn), Nat.add_zero]

theorem unitTarget_backward_count {n w : Nat} (hw : 0 < w) (hn : 2 * w + 1 < n)
    (P : Queue) (hP : ∀ x ∈ P, 2 * w + 2 ≤ x ∧ x < n) (p : Nat) :
    w < replacementCount (cycleAdjacent n) 0 ((P ++ unitTargetTail w).drop p).reverse ↔ p ≤ P.length := by
  have ht := unitTargetTail_backward hw hn
  have hpno : ∀ x ∈ P, cycleAdjacent n (w + 1) x = false := by
    intro x hx
    exact cycle_far_right (by omega) (by have := (hP x hx).1; omega) (hP x hx).2
  by_cases hp : p ≤ P.length
  · have hnone : ∀ x ∈ (P.drop p).reverse, cycleAdjacent n (w + 1) x = false := by
      intro x hx
      exact hpno x ((List.drop_sublist p P).subset (List.mem_reverse.mp hx))
    rw [List.drop_append_of_le_length hp, List.reverse_append, replacementCount_append, ht.1, ht.2,
      replacementCount_no_adj (w + 1) _ hnone]
    omega
  · have hle := backwardCount_antitone (cycleAdjacent n) (P ++ unitTargetTail w) 0
      (show P.length + 1 ≤ p by omega)
    dsimp only at hle
    have he : ((P ++ unitTargetTail w).drop (P.length + 1)).reverse = ((unitTargetTail w).drop 1).reverse := by
      simp
    rw [he, unitTargetTail_drop_backward hw hn] at hle
    omega

end OddCycle
