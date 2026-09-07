import OddCycle.UnitTargetCounts
import OddCycle.GainedPredecessor

namespace OddCycle

def unitInitialBlock (n w : Nat) : Queue := List.range' (n - w) w

theorem unitInitialBlock_length (n w : Nat) : (unitInitialBlock n w).length = w := by simp [unitInitialBlock]

theorem unitInitialBlock_concat {n w : Nat} (hw : 0 < w) (hn : w < n) :
    unitInitialBlock n w = List.range' (n - w) (w - 1) ++ [n - 1] := by
  unfold unitInitialBlock
  have hh := List.range'_1_concat (s := n - w) (n := w - 1)
  rw [show w - 1 + 1 = w by omega] at hh
  rw [hh, show n - w + (w - 1) = n - 1 by omega]

theorem unitInitialBlock_backward_count {n w : Nat} (hw : 0 < w) (hn : w < n) :
    replacementCount (cycleAdjacent n) 0 (unitInitialBlock n w).reverse = w := by
  let f := fun i => if i = 0 then 0 else n - i
  have hedges : ∀ i, 0 ≤ i → i < 0 + w → cycleAdjacent n (f i) (f (i + 1)) = true := by
    intro i _ hi
    have hf : f (i + 1) = n - (i + 1) := by simp [f]
    rw [hf]
    by_cases hz : i = 0
    · subst i
      apply (cycleAdjacent_iff (a := 0) (by omega) (by omega)).mpr
      right; right; left
      exact ⟨rfl, by omega⟩
    · rw [show f i = n - i by simp [f, hz]]
      apply (cycleAdjacent_iff (by omega) (by omega)).mpr
      exact Or.inr (Or.inl (by omega))
  have hmap : (List.range' 1 w).map f = (unitInitialBlock n w).reverse := by
    apply List.ext_getElem
    · simp [unitInitialBlock]
    · intro i hi hj
      have hiw : i < w := by simpa using hi
      simp only [List.getElem_map, List.getElem_range', one_mul, f,
        if_neg (by omega : ¬ 1 + i = 0), List.getElem_reverse, unitInitialBlock,
        List.length_range', List.getElem_range']
      omega
  have hh := replacementCount_chain (adj := cycleAdjacent n) f 0 w [] hedges
  simpa only [show f 0 = 0 by simp [f], Nat.zero_add, List.append_nil, hmap, replacementCount, Nat.add_zero] using hh

theorem unit_pattern_last {w : Nat} (hw : 0 < w) (P : Queue) :
    (P ++ unitTargetTail w).getLast? = some 1 := by
  have he : w = (w - 1) + 1 := by omega
  unfold unitTargetTail
  rw [List.getLast?_append, List.getLast?_append]
  have hh : ((List.range' 1 w).reverse).getLast? = some 1 := by
    rw [he]
    simp [List.range'_succ]
  simp [hh]

theorem unit_pattern_neighbor_index {n w : Nat} (hw : 0 < w) (hn : w < n) (tail : Queue)
    (hnd : (unitInitialBlock n w ++ tail).Nodup) :
    (unitInitialBlock n w ++ tail).idxOf (n - 1) + 1 = w := by
  rw [unitInitialBlock_concat hw hn, List.append_assoc, List.singleton_append] at hnd ⊢
  rw [idxOf_middle _ _ _ hnd]
  simp only [List.length_range']
  omega

end OddCycle
