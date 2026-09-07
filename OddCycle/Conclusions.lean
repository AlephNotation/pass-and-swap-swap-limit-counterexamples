import OddCycle.FiveJob
import OddCycle.Balance

namespace OddCycle.FiveJob

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rate_positive (job : Nat) : 0 < rate job := by
  unfold rate
  split <;> norm_num

theorem canonical_scaled_not_stationary (k : ℚ) (hk : k ≠ 0) :
    ¬ Stationary adj 2 rate support (fun s => k * canonicalWeight rate s) := by
  intro h
  have hz := h target target_mem
  rw [balance_scale, canonical_defect] at hz
  have hn : -(1 / 360 : ℚ) ≠ 0 := by norm_num
  exact (mul_ne_zero hk hn) hz

def totalWeight : ℚ := 29781619500363599243784

def probability (s : State) : ℚ := totalWeight⁻¹ * weight s

theorem weight_sum : (support.map weight).sum = totalWeight := by
  calc
    (support.map weight).sum = ((support.map integerWeight).sum : ℚ) :=
      List.sum_map_hom support integerWeight (Nat.castAddMonoidHom ℚ)
    _ = totalWeight := by rw [certificate_total]; rfl

theorem probability_positive {s : State} (hs : s ∈ support) : 0 < probability s := by
  have hw : (0 : ℚ) < weight s := by
    unfold weight
    exact_mod_cast certificate_positive s hs
  exact mul_pos (by norm_num [totalWeight]) hw

theorem probability_sum : (support.map probability).sum = 1 := by
  unfold probability
  rw [List.sum_map_mul_left, weight_sum]
  norm_num [totalWeight]

theorem probability_stationary : Stationary adj 2 rate support probability :=
  certificate_stationary.scale _

theorem probability_not_product :
    ¬ ∃ (K : ℚ) (A B : Queue → ℚ), ∀ s ∈ support, probability s = K * A s.1 * B s.2 := by
  rintro ⟨K, A, B, h⟩
  apply normalized_certificate_not_product totalWeight (by norm_num [totalWeight])
  refine ⟨K, A, B, ?_⟩
  intro s hs
  simpa [probability, weight, div_eq_mul_inv, mul_comm] using h s hs

/-- An explicit proper three-coloring places this example in the partite regime. -/
def color (i : Fin 5) : Fin 3 := if i = 4 then 2 else if i.val % 2 = 0 then 0 else 1

theorem proper_three_coloring :
    ∀ i j : Fin 5, adj i.val j.val = true → color i ≠ color j := by decide +kernel

end OddCycle.FiveJob
