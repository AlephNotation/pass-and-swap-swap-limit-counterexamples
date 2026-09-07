import OddCycle.QueueMarkov

/-! Stationary probabilities for the original queue balance equations. -/

namespace OddCycle

theorem queue_balance {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta)
    (weight : State → ℝ) (t : BalancedState w) :
    balance (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w) weight t.val =
      (theta + (2 * w : Nat)) *
        ((queueMarkov hw ht).advance (fun s => weight s.val) t - weight t.val) := by
  rw [balance_spike_at hw theta w weight t.val t.property, ← balancedState_sum hw]
  have hin (s : BalancedState w) :
      incomingRow (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (weight s.val) t.val s.val =
        weight s.val * queueIncomingRate w theta s t := by
    unfold incomingRow queueIncomingRate
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro e _
    split_ifs <;> simp
  simp_rw [hin]
  change _ = (theta + (2 * w : Nat)) *
    ((∑ s : BalancedState w, weight s.val * (queueIncomingRate w theta s t / (theta + (2 * w : Nat)))) - weight t.val)
  simp only [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
  have hn := (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg (2 * w))).ne'
  field_simp

theorem queue_stationary_iff {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta)
    (weight : State → ℝ) :
    Stationary (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w) weight ↔
      (queueMarkov hw ht).StationaryVector (fun s => weight s.val) := by
  have hn := (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg (2 * w))).ne'
  constructor
  · intro h t
    have he := h t.val t.property
    rw [queue_balance hw ht weight t] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hn)
  · intro h t htgt
    rw [queue_balance hw ht weight ⟨t, htgt⟩, h ⟨t, htgt⟩, sub_self, mul_zero]

noncomputable def extendBalancedWeight (w : Nat) (v : BalancedState w → ℝ) (s : State) : ℝ :=
  if hs : s ∈ balancedStates w then v ⟨s, hs⟩ else 0

theorem extendBalancedWeight_apply (w : Nat) (v : BalancedState w → ℝ) (s : BalancedState w) :
    extendBalancedWeight w v s.val = v s := by simp [extendBalancedWeight, s.property]

theorem queue_stationary_exists_unique {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta) :
    ∃! v : BalancedState w → ℝ, v ∈ stdSimplex ℝ (BalancedState w) ∧
      Stationary (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w) (extendBalancedWeight w v) := by
  letI : Nonempty (BalancedState w) :=
    ⟨⟨flowTarget w, (mem_balancedStates_iff hw _).mpr (flowTarget_valid_balanced hw)⟩⟩
  have he (v : BalancedState w → ℝ) :
      Stationary (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w) (extendBalancedWeight w v) ↔
        (queueMarkov hw ht).StationaryVector v := by
    rw [queue_stationary_iff hw ht]
    simp only [extendBalancedWeight_apply]
  simp_rw [he]
  exact (queueMarkov hw ht).stationary_exists_unique (queueMarkov_irreducible hw ht)

theorem queue_stationary_positive {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta)
    {v : BalancedState w → ℝ} (hv : v ∈ stdSimplex ℝ (BalancedState w))
    (hs : Stationary (cycleAdjacent (2 * w + 1)) w (spikeRate theta) (balancedStates w) (extendBalancedWeight w v)) :
    ∀ s, 0 < v s := by
  have h := (queue_stationary_iff hw ht _).mp hs
  simp only [extendBalancedWeight_apply] at h
  exact (queueMarkov hw ht).stationary_positive (queueMarkov_irreducible hw ht) hv h

theorem queue_normalized_not_stationary {w : Nat} (hw : 2 ≤ w) {theta : ℝ}
    (ht : 0 < theta) (ht1 : theta ≠ 1) :
    ¬ (queueMarkov hw ht).StationaryVector (fun s => normalizedCanonicalWeight w theta s.val) := by
  rw [← queue_stationary_iff hw ht]
  exact normalizedCanonicalWeight_not_stationary hw ht ht1

end OddCycle
