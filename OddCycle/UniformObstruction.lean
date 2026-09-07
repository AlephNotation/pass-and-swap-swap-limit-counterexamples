import OddCycle.DefectSign

/-! The canonical weights fail stationarity even after normalization. -/

namespace OddCycle

theorem uniform_defect_ne_zero {w : Nat} (hw : 2 ≤ w) {theta : ℝ}
    (ht : 0 < theta) (ht1 : theta ≠ 1) :
    balance (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w)
      (canonicalWeight (spikeRate theta)) (flowTarget w) ≠ 0 := by
  rcases lt_or_gt_of_ne ht1 with h | h
  · exact (uniform_defect_pos hw ht h).ne'
  · exact (uniform_defect_neg hw h).ne

theorem uniform_scaled_not_stationary {w : Nat} (hw : 2 ≤ w) {theta : ℝ}
    (ht : 0 < theta) (ht1 : theta ≠ 1) {k : ℝ} (hk : k ≠ 0) :
    ¬ Stationary (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w)
      (fun s => k * canonicalWeight (spikeRate theta) s) := by
  intro h
  have he := h (flowTarget w) ((mem_balancedStates_iff hw _).mpr (flowTarget_valid_balanced hw))
  rw [balance_scale] at he
  exact (mul_ne_zero hk (uniform_defect_ne_zero hw ht ht1)) he

theorem prefixWeight_pos (rate : Nat → ℝ) (hr : ∀ x, 0 < rate x) (q : Queue)
    {total : ℝ} (ht : 0 ≤ total) : 0 < prefixWeight rate total q := by
  induction q generalizing total with
  | nil => exact zero_lt_one
  | cons x q ih =>
    have hp := add_pos_of_nonneg_of_pos ht (hr x)
    exact mul_pos (inv_pos.mpr hp) (ih hp.le)

theorem spikeRate_pos {theta : ℝ} (ht : 0 < theta) (x : Nat) : 0 < spikeRate theta x := by
  unfold spikeRate
  split_ifs
  · exact ht
  · exact zero_lt_one

theorem canonicalWeight_pos (rate : Nat → ℝ) (hr : ∀ x, 0 < rate x) (s : State) :
    0 < canonicalWeight rate s :=
  mul_pos (prefixWeight_pos rate hr s.1 le_rfl) (prefixWeight_pos rate hr s.2 le_rfl)

noncomputable def normalizingConstant (w : Nat) (theta : ℝ) : ℝ :=
  ((balancedStates w).map (canonicalWeight (spikeRate theta))).sum

theorem normalizingConstant_pos {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta) :
    0 < normalizingConstant w theta := by
  apply List.sum_pos
  · intro x hx
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
    exact canonicalWeight_pos _ (spikeRate_pos ht) s
  · intro he
    have hm : canonicalWeight (spikeRate theta) (flowTarget w) ∈
        (balancedStates w).map (canonicalWeight (spikeRate theta)) := List.mem_map.mpr ⟨flowTarget w,
      (mem_balancedStates_iff hw _).mpr (flowTarget_valid_balanced hw), rfl⟩
    rw [he] at hm
    exact List.not_mem_nil hm

noncomputable def normalizedCanonicalWeight (w : Nat) (theta : ℝ) (s : State) : ℝ :=
  (normalizingConstant w theta)⁻¹ * canonicalWeight (spikeRate theta) s

theorem normalizedCanonicalWeight_pos {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta) (s : State) :
    0 < normalizedCanonicalWeight w theta s :=
  mul_pos (inv_pos.mpr (normalizingConstant_pos hw ht)) (canonicalWeight_pos _ (spikeRate_pos ht) s)

theorem normalizedCanonicalWeight_sum {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta) :
    ((balancedStates w).map (normalizedCanonicalWeight w theta)).sum = 1 := by
  unfold normalizedCanonicalWeight
  rw [List.sum_map_mul_left]
  exact inv_mul_cancel₀ (normalizingConstant_pos hw ht).ne'

theorem normalizedCanonicalWeight_not_stationary {w : Nat} (hw : 2 ≤ w) {theta : ℝ}
    (ht : 0 < theta) (ht1 : theta ≠ 1) :
    ¬ Stationary (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w)
      (normalizedCanonicalWeight w theta) :=
  uniform_scaled_not_stationary hw ht ht1 (inv_ne_zero (normalizingConstant_pos hw ht).ne')

end OddCycle
