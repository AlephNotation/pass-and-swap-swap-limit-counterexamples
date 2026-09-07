import OddCycle.TwoFlowCompleteness
import OddCycle.EventWeights
import OddCycle.GeneralCardinality

/-! Subtracting the generators leaves precisely the two exchanged flows,
for arbitrary weights and class rates over a field. -/

namespace OddCycle

theorem flowSourceX_valid_balanced {w : Nat} (hw : 2 ≤ w) :
    Valid (2 * w + 1) (flowSourceX w) ∧ balanced w (flowSourceX w) = true := by
  have hv := branchState_valid hw (show w < 2 * w + 1 by omega) false
  have hb := branchState_balanced (show w < 2 * w + 1 by omega) false
  exact ⟨hv.exchange, balanced_exchange hw hv hb⟩

theorem flowSourceY_valid_balanced {w : Nat} (hw : 2 ≤ w) :
    Valid (2 * w + 1) (flowSourceY w) ∧ balanced w (flowSourceY w) = true := by
  have hv := (flowY_frame hw).1
  have hb := balanced_of_orientation_eq (flowY_frame hw).2
    (branchState_balanced (show w < 2 * w + 1 by omega) true)
  exact ⟨hv.exchange, balanced_exchange hw hv hb⟩

theorem flowSources_ne {w : Nat} (hw : 2 ≤ w) : flowSourceX w ≠ flowSourceY w := by
  intro he
  have hq := congrArg Prod.snd he
  have h := congrArg (fun q => complete (cycleAdjacent (2 * w + 1)) w q 0) hq
  dsimp only [flowSourceX, flowSourceY] at h
  rw [(flowX_complete hw (show w < w + 1 by omega)).1,
    (flowY_complete hw (show w < w + 1 by omega)).1] at h
  have hh := congrArg (Option.map (fun r : Queue × Nat × Nat => r.2.1)) h
  simp only [Option.map_some, Option.some.injEq] at hh
  omega

variable {K : Type*} [Field K]

theorem two_flow_event_difference {w bigger pos : Nat} {s : State} {side : Bool}
    (hw : 2 ≤ w) (hbig : w < bigger) (hv : Valid (2 * w + 1) s) (hb : balanced w s = true)
    (rate : Nat → K) (weight : K) :
    incomingOption rate weight (flowTarget w) (transition (cycleAdjacent (2 * w + 1)) w s side pos) -
      incomingOption rate weight (flowTarget w) (transition (cycleAdjacent (2 * w + 1)) bigger s side pos) =
      (if s = flowSourceX w ∧ side = true ∧ pos = 0 then weight * rate w else 0) -
      (if s = flowSourceY w ∧ side = true ∧ pos = 0 then weight * rate w else 0) := by
  by_cases hx : s = flowSourceX w ∧ side = true ∧ pos = 0
  · obtain ⟨rfl, rfl, rfl⟩ := hx
    have hn : 2 * w ≠ 0 := by omega
    have hneq : ([], flowWordX w) ≠ flowSourceY w := flowSources_ne hw
    simp [incomingOption, transition, flowSourceX, (flowX_complete hw hbig).1, (flowX_complete hw hbig).2,
      flowTarget, hn, hneq]
  by_cases hy : s = flowSourceY w ∧ side = true ∧ pos = 0
  · obtain ⟨rfl, rfl, rfl⟩ := hy
    have hn : 2 * w ≠ 0 := by omega
    have hneq : ([], flowWordY w) ≠ flowSourceX w := Ne.symm (flowSources_ne hw)
    simp [incomingOption, transition, flowSourceY, (flowY_complete hw hbig).1, (flowY_complete hw hbig).2,
      flowTarget, hn, hneq]
  by_cases he : transition (cycleAdjacent (2 * w + 1)) w s side pos =
      transition (cycleAdjacent (2 * w + 1)) bigger s side pos
  · simp [he, hx, hy]
  have hfirst : incomingOption rate weight (flowTarget w)
      (transition (cycleAdjacent (2 * w + 1)) w s side pos) = 0 := by
    apply incomingOption_zero
    intro i hi
    obtain ⟨hs, hside, hpos, _⟩ := ((two_flow_completeness hw hbig hv hb he).1).mp hi
    exact hx ⟨hs, hside, hpos⟩
  have hsecond : incomingOption rate weight (flowTarget w)
      (transition (cycleAdjacent (2 * w + 1)) bigger s side pos) = 0 := by
    apply incomingOption_zero
    intro i hi
    obtain ⟨hs, hside, hpos, _⟩ := ((two_flow_completeness hw hbig hv hb he).2).mp hi
    exact hy ⟨hs, hside, hpos⟩
  simp [hfirst, hsecond, hx, hy]

theorem two_flow_row_difference {w bigger : Nat} {s : State} (hw : 2 ≤ w) (hbig : w < bigger)
    (hv : Valid (2 * w + 1) s) (hb : balanced w s = true) (rate : Nat → K) (weight : K) :
    incomingRow (cycleAdjacent (2 * w + 1)) w rate weight (flowTarget w) s -
      incomingRow (cycleAdjacent (2 * w + 1)) bigger rate weight (flowTarget w) s =
      (if s = flowSourceX w then weight * rate w else 0) -
      (if s = flowSourceY w then weight * rate w else 0) := by
  have hside (side : Bool) (positions : List Nat) :
      (positions.map (fun p => incomingOption rate weight (flowTarget w)
        (transition (cycleAdjacent (2 * w + 1)) w s side p))).sum -
      (positions.map (fun p => incomingOption rate weight (flowTarget w)
        (transition (cycleAdjacent (2 * w + 1)) bigger s side p))).sum =
      (positions.map (fun p =>
        (if s = flowSourceX w ∧ side = true ∧ p = 0 then weight * rate w else 0) -
        (if s = flowSourceY w ∧ side = true ∧ p = 0 then weight * rate w else 0))).sum := by
    rw [← sum_map_sub]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _
    exact two_flow_event_difference hw hbig hv hb rate weight
  rw [incomingRow_positions, incomingRow_positions]
  rw [show ∀ a b c d : K, (a + b) - (c + d) = (a - c) + (b - d) by intros; ring,
    hside false, hside true]
  simp only [Bool.false_eq_true, and_false, false_and, ↓reduceIte, sub_self, List.map_const',
    List.sum_replicate, smul_zero, zero_add, true_and]
  rw [sum_map_sub]
  have hsum (t : State) (ht : t = flowSourceX w ∨ t = flowSourceY w) :
      ((List.range s.2.length).map (fun p => if s = t ∧ p = 0 then weight * rate w else 0)).sum =
        if s = t then weight * rate w else 0 := by
    by_cases he : s = t
    · subst t
      have hlen : 0 < s.2.length := by
        have hl := hv.length_eq
        have hempty : s.1 = [] := by rcases ht with rfl | rfl <;> rfl
        simp only [hempty, List.nil_append, List.length_range] at hl
        omega
      simp only [true_and, ↓reduceIte]
      rw [sum_map_single List.nodup_range]
      simp [hlen]
    · simp [he]
  rw [hsum (flowSourceX w) (Or.inl rfl), hsum (flowSourceY w) (Or.inr rfl)]

/-- The exact difference of limited and unlimited balance, without assuming
any stationary distribution or the imported unlimited product-form theorem. -/
theorem two_flow_balance_difference {w bigger : Nat} (hw : 2 ≤ w) (hbig : w < bigger)
    (rate : Nat → K) (weight : State → K) :
    balance (cycleAdjacent (2 * w + 1)) w rate (balancedStates w) weight (flowTarget w) -
      balance (cycleAdjacent (2 * w + 1)) bigger rate (balancedStates w) weight (flowTarget w) =
      (weight (flowSourceX w) - weight (flowSourceY w)) * rate w := by
  rw [balance_difference_incoming]
  have he : ((balancedStates w).map (fun s =>
      incomingRow (cycleAdjacent (2 * w + 1)) w rate (weight s) (flowTarget w) s -
      incomingRow (cycleAdjacent (2 * w + 1)) bigger rate (weight s) (flowTarget w) s)) =
      (balancedStates w).map (fun s =>
        (if s = flowSourceX w then weight s * rate w else 0) -
        (if s = flowSourceY w then weight s * rate w else 0)) := by
    apply List.map_congr_left
    intro s hs
    obtain ⟨hv, hb⟩ := (mem_balancedStates_iff hw s).mp hs
    exact two_flow_row_difference hw hbig hv hb rate (weight s)
  rw [he, sum_map_sub]
  have hsum (t : State) (ht : t ∈ balancedStates w) :
      ((balancedStates w).map (fun s => if s = t then weight s * rate w else 0)).sum = weight t * rate w := by
    have heq : (fun s => if s = t then weight s * rate w else 0) =
        (fun s => if s = t then weight t * rate w else 0) := by
      funext s
      split_ifs with h <;> simp_all
    rw [heq, sum_map_single (balancedStates_nodup hw)]
    simp only [ht, ↓reduceIte]
  rw [hsum (flowSourceX w) ((mem_balancedStates_iff hw _).mpr (flowSourceX_valid_balanced hw)),
    hsum (flowSourceY w) ((mem_balancedStates_iff hw _).mpr (flowSourceY_valid_balanced hw))]
  ring

end OddCycle
