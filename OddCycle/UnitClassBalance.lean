import OddCycle.CanonicalLengthProjection

/-! Equality of the original unit-rate balance residual and the restricted
completion-kernel residual, including exact cancellation by observed length. -/

noncomputable section

namespace OddCycle

open Finset

attribute [local instance] Classical.propDecidable

theorem unit_incoming_form {n : Nat} (w : Nat) (s t : CycleState n) :
    (unitPositions n).incoming w s t = ((positions s.val).map (fun p =>
      if ∃ i, transition (cycleAdjacent n) w s.val p.1 p.2 = some (t.val, i)
      then (1 : ℝ) else 0)).sum := by
  unfold PositivePositionAllocation.incoming
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [unitPositions_rate _ _ _ ((mem_positions _ _ _).mp hp)]

namespace ClosedClass

variable {n w : Nat} {states : List State} (hc : ClosedClass n w states)

theorem unit_incoming (weight : State → ℝ) (t : ClassState states) :
    oiIncoming (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity weight
      (incomingOccurrences (cycleAdjacent n) w states t.val) =
      ∑ s : ClassState states, weight s.val * (unitPositions n).incoming w (hc.embedding s) (hc.embedding t) := by
  rw [oiIncoming_positions, ← hc.state_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [unit_incoming_form, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  obtain ⟨⟨u, i⟩, he⟩ := positions_are_events (cycleAdjacent n) w s.val hp
  have hr : oiPositionRate (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity
      s.val p.1 p.2 = 1 := unitPositions_rate _ _ _ ((mem_positions _ _ _).mp hp)
  simp only [embedding_val, oiPositionIncoming, he, Option.map_some, Option.getD_some, hr, mul_one,
    Option.some.injEq, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  simp

theorem unit_balance (hn : 0 < n) (weight : State → ℝ) (t : ClassState states) :
    oiBalance (cycleAdjacent n) w (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity states weight t.val =
      (n : ℝ) * ((hc.unitKernel hn).advance (fun s => weight s.val) t - weight t.val) := by
  have hlen := (hc.valid _ (List.mem_toFinset.mp t.property)).length_eq
  simp only [List.length_append, List.length_range] at hlen
  rw [oiBalance, hc.unit_incoming]
  simp only [unit_capacity, ← Nat.cast_add, hlen]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change _ = (n : ℝ) * ((∑ s : ClassState states, weight s.val *
    ((unitPositions n).incoming w (hc.embedding s) (hc.embedding t) / (unitPositions n).total (hc.embedding s))) - weight t.val)
  simp only [unitPositions_total, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
  field_simp

theorem unitCanonical_residual_by_length (hn : 0 < n) (k : Fin (n + 1)) :
    (∑ s : ClassState states, if hc.queueLength s = k then
      oiBalance (cycleAdjacent n) w (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity states
        (normalizedOIWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity states) s.val
      else 0) = 0 := by
  simp_rw [hc.unit_balance hn]
  have hfun : (fun s : ClassState states =>
      normalizedOIWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity states s.val) = hc.unitCanonical := rfl
  rw [hfun]
  have hp := (hc.unitCanonical_projected_stationary hn) k
  rw [← (hc.unitKernel_lumps hn).push_advance] at hp
  have hh : (∑ s : ClassState states, if hc.queueLength s = k then
      ((hc.unitKernel hn).advance hc.unitCanonical s - hc.unitCanonical s) else 0) = 0 := by
    have he (s : ClassState states) : (if hc.queueLength s = k then
        ((hc.unitKernel hn).advance hc.unitCanonical s - hc.unitCanonical s) else 0) =
        (if hc.queueLength s = k then (hc.unitKernel hn).advance hc.unitCanonical s else 0) -
          (if hc.queueLength s = k then hc.unitCanonical s else 0) := by split_ifs <;> simp
    simpa only [he, Finset.sum_sub_distrib] using sub_eq_zero.mpr hp
  calc
    _ = (n : ℝ) * ∑ s : ClassState states, if hc.queueLength s = k then
        ((hc.unitKernel hn).advance hc.unitCanonical s - hc.unitCanonical s) else 0 := by
      simp only [Finset.mul_sum, mul_ite, mul_zero, unitCanonical, embedding_val]
    _ = 0 := by rw [hh, mul_zero]

end ClosedClass
end OddCycle
