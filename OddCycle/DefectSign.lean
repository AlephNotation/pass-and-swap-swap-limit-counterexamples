import OddCycle.UniformDefect
import OddCycle.FactorialProducts
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Sign and factorial specialization of the uniform canonical defect. -/

namespace OddCycle

def interiorProduct (w : Nat) (theta : ℝ) : ℝ :=
  ∏ j ∈ Finset.range w, (theta + (w : ℝ) + (j : ℝ))

theorem shiftedProduct_split (w : Nat) (theta : ℝ) :
    shiftedProduct w theta = interiorProduct w theta * (theta + (2 * w : Nat)) := by
  unfold shiftedProduct interiorProduct
  rw [List.range_succ, List.map_append, List.prod_append]
  rw [← List.prod_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  push_cast
  ring

theorem interiorProduct_pos (w : Nat) {theta : ℝ} (ht : 0 < theta) :
    0 < interiorProduct w theta := by
  apply Finset.prod_pos
  intro j _
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem interiorProduct_strict {w : Nat} (hw : 0 < w) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    interiorProduct w a < interiorProduct w b := by
  apply Finset.prod_lt_prod_of_nonempty
  · intro j _
    exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  · intro j _
    simpa only [add_comm, add_left_comm] using
      add_lt_add_right (add_lt_add_right hab (w : ℝ)) (j : ℝ)
  · exact ⟨0, Finset.mem_range.mpr hw⟩

theorem interiorProduct_one (w : Nat) :
    (w.factorial : ℝ) * interiorProduct w 1 = ((2 * w).factorial : ℝ) := by
  have h := factorial_mul_range_product (K := ℝ) w w
  rw [← List.prod_toFinset _ List.nodup_range, List.toFinset_range] at h
  convert h using 2
  · apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring
  · congr 2
    omega

theorem uniform_defect_pos {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta) (ht1 : theta < 1) :
    0 < balance (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w)
      (canonicalWeight (spikeRate theta)) (flowTarget w) := by
  rw [uniform_defect hw ht, shiftedProduct_split]
  have hf : (0 : ℝ) < w.factorial := by exact_mod_cast Nat.factorial_pos w
  have hc : (0 : ℝ) < theta + (2 * w : Nat) := add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg _)
  have hlt := mul_lt_mul_of_pos_left (interiorProduct_strict (by omega : 0 < w) ht ht1) hf
  rw [interiorProduct_one] at hlt
  apply sub_pos.mpr
  apply one_div_lt_one_div_of_lt
  · exact mul_pos hf (mul_pos (interiorProduct_pos w ht) hc)
  · simpa only [mul_assoc] using mul_lt_mul_of_pos_right hlt hc

theorem uniform_defect_neg {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht1 : 1 < theta) :
    balance (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w)
      (canonicalWeight (spikeRate theta)) (flowTarget w) < 0 := by
  have ht : 0 < theta := lt_trans zero_lt_one ht1
  rw [uniform_defect hw ht, shiftedProduct_split]
  have hf : (0 : ℝ) < w.factorial := by exact_mod_cast Nat.factorial_pos w
  have hn : (0 : ℝ) < (2 * w).factorial := by exact_mod_cast Nat.factorial_pos (2 * w)
  have hc : (0 : ℝ) < theta + (2 * w : Nat) := add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg _)
  have hlt := mul_lt_mul_of_pos_left (interiorProduct_strict (by omega : 0 < w) zero_lt_one ht1) hf
  rw [interiorProduct_one] at hlt
  apply sub_neg.mpr
  apply one_div_lt_one_div_of_lt (mul_pos hn hc)
  simpa only [mul_assoc] using mul_lt_mul_of_pos_right hlt hc

theorem uniform_defect_two {K : Type*} [Field K] [CharZero K] {w : Nat} (hw : 2 ≤ w) :
    balance (cycleAdjacent (2 * w + 1)) w (spikeRate (2 : K)) (balancedStates w)
      (canonicalWeight (spikeRate (2 : K))) (flowTarget w) = -(w : K) / ((2 * w + 2).factorial : K) := by
  have ht : (2 : K) ≠ 0 := by norm_num
  have ht1 : (2 : K) + 1 ≠ 0 := by norm_num
  have htn : (2 : K) + (2 * w : Nat) ≠ 0 := by
    have h : (((2 * w + 2 : Nat)) : K) ≠ 0 := by exact_mod_cast (show 2 * w + 2 ≠ 0 by omega)
    simpa [add_comm] using h
  rw [uniform_two_flow_identity hw 2 ht ht1 htn, flowSourceX_weight_two hw, flowSourceY_weight_two hw]
  push_cast
  ring

end OddCycle
