import OddCycle.UnlimitedTargetBalance
import OddCycle.UniformWeights
import Mathlib.Data.Real.Basic

/-! The uniform two-flow identity and canonical balance defect. -/

namespace OddCycle

variable {K : Type*} [Field K] [CharZero K]

theorem uniform_two_flow_identity {w : Nat} (hw : 2 ≤ w) (theta : K)
    (ht : theta ≠ 0) (ht1 : theta + 1 ≠ 0) (htn : theta + (2 * w : Nat) ≠ 0) :
    balance (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w)
      (canonicalWeight (spikeRate theta)) (flowTarget w) =
      canonicalWeight (spikeRate theta) (flowSourceX w) - canonicalWeight (spikeRate theta) (flowSourceY w) := by
  have h := two_flow_balance_difference hw (show w < 2 * w + 1 by omega)
    (spikeRate theta) (canonicalWeight (spikeRate theta))
  rw [unlimited_target_balance hw theta ht ht1 htn, sub_zero,
    show spikeRate theta w = 1 by simp [spikeRate, show w ≠ 0 by omega], mul_one] at h
  exact h

theorem uniform_defect_field {w : Nat} (hw : 2 ≤ w) (theta : K)
    (ht : theta ≠ 0) (ht1 : theta + 1 ≠ 0) (htn : theta + (2 * w : Nat) ≠ 0) :
    balance (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w)
      (canonicalWeight (spikeRate theta)) (flowTarget w) =
      1 / ((w.factorial : K) * shiftedProduct w theta) -
        1 / (((2 * w).factorial : K) * (theta + (2 * w : Nat))) := by
  rw [uniform_two_flow_identity hw theta ht ht1 htn, flowSourceX_weight hw theta, flowSourceY_weight hw theta]
  simp [div_eq_mul_inv, mul_comm]

/-- The displayed balance formula holds for every positive real distinguished rate. -/
theorem uniform_defect {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta) :
    balance (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w)
      (canonicalWeight (spikeRate theta)) (flowTarget w) =
      1 / ((w.factorial : ℝ) * shiftedProduct w theta) -
        1 / (((2 * w).factorial : ℝ) * (theta + (2 * w : Nat))) :=
  uniform_defect_field hw theta ht.ne' (add_pos ht zero_lt_one).ne'
    (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg _)).ne'

end OddCycle
