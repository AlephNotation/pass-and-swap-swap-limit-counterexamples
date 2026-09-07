import OddCycle.CutMarginal
import OddCycle.FiniteStationary

/-! The canonical length marginal satisfies the birth--death balance equations,
even on classes where the full canonical weight is not stationary. -/

noncomputable section

namespace OddCycle

open Finset

theorem lengthWeight_succ_mul (μ : Nat → ℝ) (k : Nat) (hμ : μ (k + 1) ≠ 0) :
    lengthWeight μ (k + 1) * μ (k + 1) = lengthWeight μ k := by
  simp only [lengthWeight, mul_assoc, inv_mul_cancel₀ hμ, mul_one]

theorem lengthWeight_pos {n : Nat} (μ : Nat → ℝ)
    (hμ : ∀ j, 1 ≤ j → j ≤ n → 0 < μ j) (k : Nat) (hk : k ≤ n) :
    0 < lengthWeight μ k := by
  induction k with
  | zero => exact zero_lt_one
  | succ k ih => exact mul_pos (ih (by omega)) (inv_pos.mpr (hμ _ (by omega) hk))

theorem lengthCanonicalWeight_pos {n : Nat} (μ ν : Nat → ℝ)
    (hμ : ∀ j, 1 ≤ j → j ≤ n → 0 < μ j)
    (hν : ∀ j, 1 ≤ j → j ≤ n → 0 < ν j) (k : Nat) (hk : k ≤ n) :
    0 < lengthCanonicalWeight n μ ν k :=
  mul_pos (lengthWeight_pos μ hμ k hk) (lengthWeight_pos ν hν (n - k) (by omega))

def lengthLaw (n : Nat) (μ ν : Nat → ℝ) (k : Fin (n + 1)) : ℝ :=
  lengthCanonicalWeight n μ ν k.val / ∑ j : Fin (n + 1), lengthCanonicalWeight n μ ν j.val

theorem lengthLaw_simplex {n : Nat} (μ ν : Nat → ℝ)
    (hμ : ∀ j, 1 ≤ j → j ≤ n → 0 < μ j)
    (hν : ∀ j, 1 ≤ j → j ≤ n → 0 < ν j) :
    lengthLaw n μ ν ∈ stdSimplex ℝ (Fin (n + 1)) := by
  have hp (j : Fin (n + 1)) : 0 < lengthCanonicalWeight n μ ν j.val :=
    lengthCanonicalWeight_pos μ ν hμ hν j.val (by have := j.isLt; omega)
  have hZ : 0 < ∑ j : Fin (n + 1), lengthCanonicalWeight n μ ν j.val :=
    Finset.sum_pos (fun j _ => hp j) Finset.univ_nonempty
  constructor
  · intro j; exact (div_pos (hp j) hZ).le
  · simp only [lengthLaw, div_eq_mul_inv, ← Finset.sum_mul, mul_inv_cancel₀ hZ.ne']

theorem lengthCanonical_detailed_balance {n : Nat} (μ ν : Nat → ℝ)
    (k : Nat) (hk : k < n) (hμ : μ (k + 1) ≠ 0) (hν : ν (n - k) ≠ 0) :
    lengthCanonicalWeight n μ ν k * ν (n - k) =
      lengthCanonicalWeight n μ ν (k + 1) * μ (k + 1) := by
  have hb : lengthWeight ν (n - k) * ν (n - k) = lengthWeight ν (n - (k + 1)) := by
    have he : n - (k + 1) + 1 = n - k := by omega
    simpa only [he] using lengthWeight_succ_mul ν (n - (k + 1)) (by rwa [he])
  unfold lengthCanonicalWeight
  calc
    _ = lengthWeight μ k * (lengthWeight ν (n - k) * ν (n - k)) := by ring
    _ = lengthWeight μ k * lengthWeight ν (n - (k + 1)) := by rw [hb]
    _ = (lengthWeight μ (k + 1) * μ (k + 1)) * lengthWeight ν (n - (k + 1)) := by
      rw [lengthWeight_succ_mul μ k hμ]
    _ = _ := by ring

theorem lengthCanonical_generator_sum {n : Nat} (μ ν : Nat → ℝ)
    (hμ0 : μ 0 = 0) (hν0 : ν 0 = 0)
    (hμ : ∀ j, 1 ≤ j → j ≤ n → μ j ≠ 0)
    (hν : ∀ j, 1 ≤ j → j ≤ n → ν j ≠ 0) (f : Nat → ℝ) :
    (∑ k ∈ Finset.range (n + 1), lengthCanonicalWeight n μ ν k *
      (μ k * (f (k - 1) - f k) + ν (n - k) * (f (k + 1) - f k))) = 0 := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun k => lengthCanonicalWeight n μ ν k *
    (μ k * (f (k - 1) - f k))),
    Finset.sum_range_succ (fun k => lengthCanonicalWeight n μ ν k *
    (ν (n - k) * (f (k + 1) - f k)))]
  simp only [hμ0, Nat.sub_self, hν0, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hb := lengthCanonical_detailed_balance μ ν k hk'
    (hμ _ (by omega) (by omega)) (hν _ (by omega) (by omega))
  rw [← mul_assoc, ← mul_assoc, ← hb]
  ring

/-- All functions of queue length have zero expected generator under the
canonical class weight. This does not claim balance for arbitrary observables. -/
theorem ClosedClass.canonical_length_observables {n w : Nat} {states : List State}
    (hc : ClosedClass n w states) (μ ν : Nat → ℝ)
    (hμ0 : μ 0 = 0) (hν0 : ν 0 = 0)
    (hμ : ∀ j, 1 ≤ j → j ≤ n → μ j ≠ 0)
    (hν : ∀ j, 1 ≤ j → j ≤ n → ν j ≠ 0) (f : Nat → ℝ) :
    (∑ s : ↥states.toFinset,
      oiCanonicalWeight (byLengthCapacity μ hμ0) (byLengthCapacity ν hν0) s.val *
      lengthGenerator (cycleAdjacent n) w (fun p => μ (p + 1) - μ p)
        (fun p => ν (p + 1) - ν p) s.val f) = 0 := by
  simp_rw [oiCanonicalWeight_byLength (hc.valid _ (List.mem_toFinset.mp (Subtype.property _))) μ ν hμ0 hν0,
    capacity_lengthGenerator (hc.valid _ (List.mem_toFinset.mp (Subtype.property _))) _ _ μ ν hμ0 hν0]
  rw [hc.length_weight_sum (fun k => lengthCanonicalWeight n μ ν k *
    (μ k * (f (k - 1) - f k) + ν (n - k) * (f (k + 1) - f k))),
    Fin.sum_univ_eq_sum_range (fun k => lengthCanonicalWeight n μ ν k *
      (μ k * (f (k - 1) - f k) + ν (n - k) * (f (k + 1) - f k))) (n + 1),
    lengthCanonical_generator_sum μ ν hμ0 hν0 hμ hν, mul_zero]

end OddCycle
