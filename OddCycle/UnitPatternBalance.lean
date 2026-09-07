import OddCycle.UnitGainedPredecessors
import OddCycle.AdditiveOI

/-! Exact unit-rate residual after the gained and lost predecessor lists
have been proved complete. Support membership is retained explicitly. -/

namespace OddCycle

theorem unit_changed_occurrence_weight {n small big : Nat} {rest : Queue} {o : Occurrence}
    (hsmall : 1 ≤ small) (hbig : 1 ≤ big) (hv : Valid n o.source)
    (he : transition (cycleAdjacent n) small o.source o.side o.pos = some (([0], rest), o.initiating))
    (hne : transition (cycleAdjacent n) big o.source o.side o.pos ≠ some (([0], rest), o.initiating)) :
    oiCanonicalWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity o.source *
      oiPositionRate (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity o.source o.side o.pos =
        (n.factorial : ℝ)⁻¹ := by
  have hside : o.side = true := by
    cases hh : o.side with
    | true => rfl
    | false =>
      have hf := he
      rw [hh] at hf
      have hstable := first_singleton_budget_stable hsmall hbig hf
      exact False.elim (hne (by rw [hh]; exact hstable.symm.trans hf))
  rw [hside] at he
  have hempty := (second_singleton_complete he).1
  have hlen : o.source.2.length = n := by
    have hh := hv.length_eq
    simpa only [hempty, List.nil_append, List.length_range] using hh
  have hp : o.pos < o.source.2.length := transition_pos_lt he
  have hw : oiCanonicalWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity o.source =
      (n.factorial : ℝ)⁻¹ := by
    simp only [unit_canonicalWeight, hempty, List.length_nil, Nat.factorial_zero,
      Nat.cast_one, inv_one, one_mul, hlen]
  simp [hw, oiPositionRate, hside, unit_increment (n := n) _ _ hp]

theorem oiIncoming_unit_changed {n small big : Nat} {states : List State}
    (hs : ∀ s ∈ states, Valid n s) (hsmall : 1 ≤ small) (hbig : 1 ≤ big) (rest : Queue) :
    oiIncoming (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity
      (oiCanonicalWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity)
      (gainedOccurrences (cycleAdjacent n) small big states ([0], rest)) =
        ((gainedOccurrences (cycleAdjacent n) small big states ([0], rest)).length : ℝ) * (n.factorial : ℝ)⁻¹ := by
  unfold oiIncoming
  have hm := List.map_congr_left (l := gainedOccurrences (cycleAdjacent n) small big states ([0], rest))
    (fun o ho => by
      obtain ⟨ho, he, hne⟩ := mem_gainedOccurrences.mp ho
      exact unit_changed_occurrence_weight hsmall hbig (hs _ ho) he hne)
  rw [hm]
  simp

theorem unit_pattern_balance {n w : Nat} {states : List State} (hw : 1 ≤ w) (hn : 2 * w + 1 < n)
    (hs : OrientationSupport n states) (R : Queue)
    (hP : ∀ x ∈ unitInitialBlock n w ++ R, 2 * w + 2 ≤ x ∧ x < n)
    (ht : unitPatternTarget n w R ∈ states) (hg : (unitGainOccurrence n w R).source ∈ states) :
    oiBalance (cycleAdjacent n) w (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity states
      (oiCanonicalWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity)
      (unitPatternTarget n w R) =
        (1 - (((unitInitialBlock n w ++ R).length + 1 : Nat) : ℝ)) / (n.factorial : ℝ) := by
  have hu := positive_unlimited_oi_stationary (by omega : 0 < n) hs (unitAllocation n) (unitAllocation n) _ ht
  have hdiff := oiBalance_difference_gained (cycleAdjacent n) w n
    (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity states hs.nodup
    (oiCanonicalWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity) (unitPatternTarget n w R)
  rw [hu, sub_zero] at hdiff
  have hgain := (unit_gained_predecessors hw (by omega) hs R ht hg).length_eq
  have hlost := (unit_lost_predecessors hw hn hs (unitInitialBlock n w ++ R) hP ht).length_eq
  simp only [List.length_singleton] at hgain
  simp only [List.length_map, List.length_range] at hlost
  simp only [unitPatternTarget] at hdiff hgain ⊢
  rw [oiIncoming_unit_changed hs.valid hw (by omega), oiIncoming_unit_changed hs.valid (by omega) hw,
    hgain, hlost] at hdiff
  rw [hdiff]
  simp only [Nat.cast_one, one_mul, div_eq_mul_inv, sub_mul]

end OddCycle
