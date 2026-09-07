import OddCycle.QueueLengthPathLaw
import OddCycle.UnitClassBalance
import OddCycle.NineJobCycle

/-! Exact queue-length indistinguishability on C_(2kw+1), w ≥ 1, k ≥ 2:
unit rates at every occupied position, a nonstationary normalized canonical
initialization, and the same entire observed trajectory law as an actual
stationary initialization of the same continuous-time queue process. -/

noncomputable section

namespace OddCycle

open MeasureTheory
open scoped ENNReal NNReal

theorem unit_exceptional_normalized_residual {n w k : Nat}
    (hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1) :
    let μ := (unitAllocation n).toOICapacity
    let C := exceptionalStates n w
    oiBalance (cycleAdjacent n) w μ μ C (normalizedOIWeight μ μ C)
      (unitPatternTarget n w (unitInterior n w k).reverse) =
      (oiNormalizer μ μ C)⁻¹ * ((1 - (2 * w * (k - 1) : Nat)) / (n.factorial : ℝ)) := by
  dsimp only
  unfold normalizedOIWeight
  rw [oiBalance_scale, unit_exceptional_residual hw hk hn]

theorem unit_exceptional_normalized_residual_neg {n w k : Nat}
    (hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1) :
    let μ := (unitAllocation n).toOICapacity
    let C := exceptionalStates n w
    oiBalance (cycleAdjacent n) w μ μ C (normalizedOIWeight μ μ C)
      (unitPatternTarget n w (unitInterior n w k).reverse) < 0 := by
  dsimp only
  rw [unit_exceptional_normalized_residual hw hk hn]
  have hc := exceptionalStates_closedClass hw (by omega : 1 ≤ k) hn
  have hZ := oiNormalizer_pos (unitAllocation n) (unitAllocation n) hc.valid hc.nonempty
  have hnum : 1 < 2 * w * (k - 1) := by
    nlinarith [Nat.mul_le_mul_right (2 * w) (show 1 ≤ k - 1 by omega)]
  have hnum' : (1 : ℝ) < (2 * w * (k - 1) : Nat) := by exact_mod_cast hnum
  have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hZ) (div_neg_of_neg_of_pos (sub_neg.mpr hnum') hfact)

theorem unit_exceptional_canonical_not_fixed {n w k : Nat}
    (hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1) :
    let hc := exceptionalStates_closedClass hw (by omega : 1 ≤ k) hn
    ¬ (hc.unitKernel (by omega : 0 < n)).StationaryVector hc.unitCanonical := by
  dsimp only
  intro hstat
  let hc := exceptionalStates_closedClass hw (by omega : 1 ≤ k) hn
  let s := unitPatternTarget n w (unitInterior n w k).reverse
  have hs : s ∈ exceptionalStates n w := mem_exceptionalStates.mpr
    ⟨unitPatternTarget_valid (by nlinarith [Nat.mul_le_mul_right w hk]) (unitInterior_perm hw hk hn),
      unit_target_exceptional hw hk hn⟩
  have he := hc.unit_balance (by omega : 0 < n)
    (normalizedOIWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity (exceptionalStates n w))
    ⟨s, List.mem_toFinset.mpr hs⟩
  change _ = (n : ℝ) * ((hc.unitKernel (by omega)).advance hc.unitCanonical ⟨s, List.mem_toFinset.mpr hs⟩ -
    hc.unitCanonical ⟨s, List.mem_toFinset.mpr hs⟩) at he
  rw [hstat _, sub_self, mul_zero] at he
  have hneg := unit_exceptional_normalized_residual_neg hw hk hn
  change _ < 0 at hneg
  rw [he] at hneg
  exact lt_irrefl 0 hneg

/-- The comparison initialization is stationary at every physical time, while
the canonical initialization has a strictly negative full balance residual.
Their laws on the complete continuous queue-length trajectory are equal. -/
theorem unit_exceptional_queue_length_indistinguishability {n w k : Nat}
    (hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1) :
    let C := exceptionalStates n w
    let hc := exceptionalStates_closedClass hw (by omega : 1 ≤ k) hn
    let η := hc.unitCanonical
    let μ := (unitAllocation n).toOICapacity
    η ∈ stdSimplex ℝ (ClassState C) ∧
      ¬ (hc.unitKernel (by omega : 0 < n)).StationaryVector η ∧
      ∃ π : ClassState C → ℝ, π ∈ stdSimplex ℝ (ClassState C) ∧
        (hc.unitKernel (by omega : 0 < n)).StationaryVector π ∧
        (∀ t : ℝ≥0, ∀ j : CycleState n,
          hc.configurationLaw (by omega) π {y | y t = j} = ENNReal.ofReal (hc.fullInitial π j)) ∧
        hc.lengthPathLaw (by omega) η = hc.lengthPathLaw (by omega) π ∧
        (∀ j : Fin (n + 1), (∑ s : ClassState C, if hc.queueLength s = j then
          oiBalance (cycleAdjacent n) w μ μ C (normalizedOIWeight μ μ C) s.val else 0) = 0) ∧
        oiBalance (cycleAdjacent n) w μ μ C (normalizedOIWeight μ μ C)
          (unitPatternTarget n w (unitInterior n w k).reverse) < 0 := by
  dsimp only
  let hc := exceptionalStates_closedClass hw (by omega : 1 ≤ k) hn
  obtain ⟨π, hπ, hstat⟩ := hc.unit_stationary_exists (by omega : 0 < n)
  exact ⟨hc.unitCanonical_simplex, unit_exceptional_canonical_not_fixed hw hk hn,
    π, hπ, hstat, hc.configurationLaw_stationary_current (by omega) hπ hstat,
    hc.canonical_queue_length_indistinguishable (by omega) hπ hstat,
    hc.unitCanonical_residual_by_length (by omega), unit_exceptional_normalized_residual_neg hw hk hn⟩

namespace NineJobCycle

theorem queue_length_indistinguishability :
    let hc := recurrent_class
    let μ := (unitAllocation 9).toOICapacity
    ∃ π : ClassState (exceptionalStates 9 2) → ℝ,
      π ∈ stdSimplex ℝ (ClassState (exceptionalStates 9 2)) ∧
      (hc.unitKernel (by omega)).StationaryVector π ∧
      (∀ t : ℝ≥0, ∀ j : CycleState 9,
        hc.configurationLaw (by omega) π {y | y t = j} = ENNReal.ofReal (hc.fullInitial π j)) ∧
      hc.lengthPathLaw (by omega) hc.unitCanonical = hc.lengthPathLaw (by omega) π ∧
      oiBalance (cycleAdjacent 9) 2 μ μ (exceptionalStates 9 2)
        (normalizedOIWeight μ μ (exceptionalStates 9 2)) target < 0 := by
  obtain ⟨_, _, π, hπ, hstat, htime, hpath, _, hneg⟩ :=
    unit_exceptional_queue_length_indistinguishability (n := 9) (w := 2) (k := 2) (by omega) (by omega) rfl
  rw [target_eq] at hneg
  exact ⟨π, hπ, hstat, htime, hpath, hneg⟩

end NineJobCycle
end OddCycle
