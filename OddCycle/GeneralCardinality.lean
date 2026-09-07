import OddCycle.BalancedWords
import Mathlib.Data.Finset.Card

/-! The exact number of valid balanced states for every swap limit w ≥ 2. -/

namespace OddCycle

def cutState (q : Queue) (k : Nat) : State := (q.take k, (q.drop k).reverse)

theorem placement_cutState (q : Queue) (k : Nat) : placement (cutState q k) = q := by
  simp [placement, cutState]

theorem cutState_placement (s : State) : cutState (placement s) s.1.length = s := by
  simp [placement, cutState]

theorem valid_iff_placement_valid (n : Nat) (s : State) :
    Valid n s ↔ Valid n (placement s, []) := by
  constructor
  · intro h
    simpa [Valid] using h.placement_perm
  · intro h
    exact ((List.reverse_perm s.2).append_left s.1).symm.trans (by simpa [Valid] using h)

theorem balanced_placement (w : Nat) (s : State) : balanced w (placement s, []) = balanced w s := by
  simp [balanced, orientation, placement]

def wordCuts (q : Queue) : List State := (List.range (q.length + 1)).map (cutState q)

theorem mem_wordCuts_iff (q : Queue) (s : State) : s ∈ wordCuts q ↔ placement s = q := by
  constructor
  · intro h
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp h
    exact placement_cutState q k
  · intro h
    apply List.mem_map.mpr
    refine ⟨s.1.length, ?_, ?_⟩
    · rw [List.mem_range, ← h]
      simp [placement]
    · rw [← h, cutState_placement]

theorem wordCuts_nodup (q : Queue) : (wordCuts q).Nodup := by
  apply List.nodup_range.map_on
  intro i hi j hj he
  have hi' : i ≤ q.length := by have := List.mem_range.mp hi; omega
  have hj' : j ≤ q.length := by have := List.mem_range.mp hj; omega
  have hh := congrArg (fun s : State => s.1.length) he
  simpa [cutState, List.length_take, Nat.min_eq_left hi', Nat.min_eq_left hj'] using hh

def balancedStates (w : Nat) : List State := (balancedWords w).flatMap wordCuts

theorem mem_balancedStates_iff {w : Nat} (hw : 2 ≤ w) (s : State) :
    s ∈ balancedStates w ↔ Valid (2 * w + 1) s ∧ balanced w s = true := by
  simp only [balancedStates, List.mem_flatMap, mem_wordCuts_iff]
  constructor
  · rintro ⟨q, hq, heq⟩
    subst q
    obtain ⟨hv, hb⟩ := (mem_balancedWords_iff hw _).mp hq
    exact ⟨(valid_iff_placement_valid _ _).mpr hv, by simpa only [balanced_placement] using hb⟩
  · rintro ⟨hv, hb⟩
    exact ⟨placement s, (mem_balancedWords_iff hw _).mpr
      ⟨(valid_iff_placement_valid _ _).mp hv, by simpa only [balanced_placement] using hb⟩, rfl⟩

theorem balancedStates_nodup {w : Nat} (hw : 2 ≤ w) : (balancedStates w).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun q _ => wordCuts_nodup q, (balancedWords_nodup hw).imp ?_⟩
  intro a b hab s ha hb
  exact hab (((mem_wordCuts_iff a s).mp ha).symm.trans ((mem_wordCuts_iff b s).mp hb))

theorem balancedStates_length {w : Nat} (hw : 2 ≤ w) :
    (balancedStates w).length = 2 * (2 * w + 1) * (2 * w + 2) * Nat.choose (2 * w - 1) w := by
  have hlen (q : Queue) (hq : q ∈ balancedWords w) : (wordCuts q).length = 2 * w + 2 := by
    have hv := ((mem_balancedWords_iff hw q).mp hq).1
    have hl := hv.length_eq
    simp only [List.length_append, List.length_nil, Nat.add_zero, List.length_range] at hl
    simp [wordCuts, hl]
  rw [balancedStates, List.length_flatMap]
  have hmap : (balancedWords w).map (fun q => (wordCuts q).length) =
      (balancedWords w).map (fun _ => 2 * w + 2) := List.map_congr_left hlen
  rw [hmap]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, balancedWords_length]
  rw [show w + (w - 1) = 2 * w - 1 by omega]
  ring

/-- Lemma 2's cardinality, for the original exhaustive state space and balanced predicate. -/
theorem balanced_cardinality {w : Nat} (hw : 2 ≤ w) :
    ((allStates (2 * w + 1)).filter (balanced w)).toFinset.card =
      2 * (2 * w + 1) * (2 * w + 2) * Nat.choose (2 * w - 1) w := by
  have heq : ((allStates (2 * w + 1)).filter (balanced w)).toFinset =
      (balancedStates w).toFinset := by
    ext s
    simp only [List.mem_toFinset, List.mem_filter, mem_allStates_iff, mem_balancedStates_iff hw]
  rw [heq, List.toFinset_card_of_nodup (balancedStates_nodup hw), balancedStates_length hw]

end OddCycle
