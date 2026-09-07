import OddCycle.ClosedClasses
import OddCycle.UnitExceptionalFailure
import OddCycle.AdditiveGenerator
import OddCycle.UniformObstruction

namespace OddCycle

noncomputable def rateTwoAllocation (n : Nat) : PositiveOIAllocation n :=
  positiveAdditiveAllocation n (spikeRate (2 : ℝ)) (by intro x _; unfold spikeRate; split_ifs <;> norm_num)

theorem rate_two_not_oi_stationary {w : Nat} (hw : 2 ≤ w) :
    ¬ OIStationary (cycleAdjacent (2 * w + 1)) w (rateTwoAllocation (2 * w + 1)).toOICapacity
      (rateTwoAllocation (2 * w + 1)).toOICapacity (balancedStates w)
      (oiCanonicalWeight (rateTwoAllocation (2 * w + 1)).toOICapacity (rateTwoAllocation (2 * w + 1)).toOICapacity) := by
  intro hs
  have ht := (mem_balancedStates_iff hw _).mpr (flowTarget_valid_balanced hw)
  have he := hs _ ht
  change oiBalance _ _ (additiveCapacity (spikeRate (2 : ℝ))) (additiveCapacity (spikeRate (2 : ℝ))) _ (oiCanonicalWeight (additiveCapacity (spikeRate (2 : ℝ))) (additiveCapacity (spikeRate (2 : ℝ)))) _ = 0 at he
  rw [show oiCanonicalWeight (additiveCapacity (spikeRate (2 : ℝ))) (additiveCapacity (spikeRate (2 : ℝ))) =
    canonicalWeight (spikeRate (2 : ℝ)) from funext (additive_canonicalWeight _)] at he
  rw [oiBalance_additive _ _ _ _ (balancedStates_nodup hw) _ _ ht] at he
  exact uniform_defect_ne_zero hw (by norm_num) (by norm_num) he

/-- Canonical product form is universally valid on recurrent classes exactly
at the nonexceptional cycle lengths. The class predicate uses the original
queue transitions; both counterexample allocations have positive increments. -/
theorem cycle_canonical_sharpness {n w : Nat} (hn : 3 ≤ n) (hw : 2 ≤ w) :
    (∀ (μ ν : PositiveOIAllocation n) (states : List State), ClosedClass n w states →
      OIStationary (cycleAdjacent n) w μ.toOICapacity ν.toOICapacity states
        (oiCanonicalWeight μ.toOICapacity ν.toOICapacity)) ↔ n % (2 * w) ≠ 1 := by
  constructor
  · intro hall hmod
    obtain ⟨k, hk, he⟩ := (exceptional_length_iff_mod hn (by omega)).mpr hmod
    by_cases hk1 : k = 1
    · subst k
      have hn' : n = 2 * w + 1 := by simpa using he
      subst n
      exact rate_two_not_oi_stationary hw
        (hall (rateTwoAllocation _) (rateTwoAllocation _) (balancedStates w) (balancedStates_closedClass hw))
    · exact unit_exceptional_not_stationary (by omega) (by omega : 2 ≤ k) he
        (hall (unitAllocation n) (unitAllocation n) (exceptionalStates n w)
          (exceptionalStates_closedClass (by omega) hk he))
  · intro hmod μ ν states hc
    exact hc.safe_oi_stationary hn (by omega) hmod μ ν

theorem cycle_normalized_canonical_sharpness {n w : Nat} (hn : 3 ≤ n) (hw : 2 ≤ w) :
    (∀ (μ ν : PositiveOIAllocation n) (states : List State), ClosedClass n w states →
      OIStationary (cycleAdjacent n) w μ.toOICapacity ν.toOICapacity states
        (normalizedOIWeight μ.toOICapacity ν.toOICapacity states)) ↔ n % (2 * w) ≠ 1 := by
  rw [← cycle_canonical_sharpness hn hw]
  constructor
  · intro hall μ ν states hc
    exact (normalizedOI_stationary_iff (oiNormalizer_pos μ ν hc.valid hc.nonempty).ne').mp (hall μ ν states hc)
  · intro hall μ ν states hc
    exact normalizedOI_stationary (hall μ ν states hc)

end OddCycle
