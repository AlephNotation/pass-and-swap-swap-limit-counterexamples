import OddCycle.UnitGainGeometry
import OddCycle.ExceptionalSupport
import OddCycle.UnitPatternBalance

namespace OddCycle

theorem unit_target_exceptional {n w k : Nat} (hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1) :
    ExceptionalRuns n w (unitPatternTarget n w (unitInterior n w k).reverse) := by
  unfold ExceptionalRuns cycleRuns
  rw [unit_target_orientation hw hk hn]
  exact exceptional_encoding_runs hw (by omega) true

theorem unit_gain_exceptional {n w k : Nat} (hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1) :
    ExceptionalRuns n w (unitGainOccurrence n w (unitInterior n w k).reverse).source := by
  have hsize : 3 * w + 2 ≤ n := by nlinarith [Nat.mul_le_mul_right w hk]
  have hv := unitPatternTarget_valid hsize (unitInterior_perm hw hk hn)
  have hflip := unit_gain_edge_flip hw hsize (unitInterior n w k).reverse hv
  have hf := (rotatedFlipAt_iff_edgeBitFlip (n := n) (i := 0) 0 (by omega)).mpr
    (by simpa only [Nat.zero_add, Nat.zero_mod] using hflip)
  simp only [List.rotate_zero, unit_target_orientation hw hk hn] at hf
  have hsource := CircularWord.flipAt_first_prefix (unitOrientation_start (w := w) hk) hf
  have hmove : CircularWord.LinearFlip w (unitOrientation w k)
      (orientation n (unitGainOccurrence n w (unitInterior n w k).reverse).source) := by
    rw [hsource, unitOrientation_start hk]
    exact CircularWord.LinearFlip.first [] _ true
  exact CircularRun.exceptional_reachable (exceptional_encoding_runs hw (by omega) true)
    (hmove.run_reachable hw (exceptional_encoding_nonconstant hw (by omega) true))

theorem unit_exceptional_residual {n w k : Nat} (hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1) :
    oiBalance (cycleAdjacent n) w (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity
      (exceptionalStates n w)
      (oiCanonicalWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity)
      (unitPatternTarget n w (unitInterior n w k).reverse) =
        (1 - (2 * w * (k - 1) : Nat)) / (n.factorial : ℝ) := by
  have hsize : 3 * w + 2 ≤ n := by nlinarith [Nat.mul_le_mul_right w hk]
  have hH := unitInterior_perm hw hk hn
  have hv := unitPatternTarget_valid hsize hH
  have ht := mem_exceptionalStates.mpr ⟨hv, unit_target_exceptional hw hk hn⟩
  have hg := mem_exceptionalStates.mpr ⟨unit_gain_valid hv, unit_gain_exceptional hw hk hn⟩
  have he := unit_pattern_balance hw (by omega) (exceptionalStates_support n w)
    (unitInterior n w k).reverse (unitPattern_prefix_labels hw hsize hH) ht hg
  have hlen : (unitInitialBlock n w ++ (unitInterior n w k).reverse).length + 1 = 2 * w * (k - 1) := by
    have hh := hH.length_eq
    simp only [List.length_range'] at hh
    simp only [List.length_append, List.length_reverse, unitInitialBlock_length, hh]
    have hk' : k = (k - 1) + 1 := by omega
    have hsub := Nat.sub_add_cancel hsize
    nlinarith
  simpa only [hlen] using he

theorem unit_exceptional_not_stationary {n w k : Nat} (hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1) :
    ¬ OIStationary (cycleAdjacent n) w (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity
      (exceptionalStates n w) (oiCanonicalWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity) := by
  intro hs
  have ht := mem_exceptionalStates.mpr ⟨unitPatternTarget_valid (by nlinarith [Nat.mul_le_mul_right w hk])
    (unitInterior_perm hw hk hn), unit_target_exceptional hw hk hn⟩
  have he := hs _ ht
  rw [unit_exceptional_residual hw hk hn] at he
  have hnum : 1 < (2 * w * (k - 1) : Nat) := by nlinarith [Nat.mul_le_mul_right (2 * w) (show 1 ≤ k - 1 by omega)]
  have hreal : (1 : ℝ) < (2 * w * (k - 1) : Nat) := by exact_mod_cast hnum
  have hfact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hneg := div_neg_of_neg_of_pos (sub_neg.mpr hreal) hfact
  linarith

end OddCycle
