import OddCycle.FiniteEvolution

/-! A stationary-flow lower bound for mixing, without reversibility.
Every premise is an ordinary probability-vector or transition-kernel property. -/

noncomputable section

namespace OddCycle.FiniteMarkov

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S] (P : FiniteMarkov S)

def outflow (v : S → ℝ) (A : Finset S) : ℝ := ∑ i ∈ A, v i * ∑ j ∈ Aᶜ, P.prob i j

theorem outflow_nonneg {v : S → ℝ} (hv : ∀ i, 0 ≤ v i) (A : Finset S) :
    0 ≤ P.outflow v A :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (Finset.sum_nonneg (fun j _ => P.nonneg i j)))

theorem outflow_dominated {v π : S → ℝ} {c : ℝ} (h : ∀ i, v i ≤ c * π i) (A : Finset S) :
    P.outflow v A ≤ c * P.outflow π A := by
  simp only [outflow, Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_right (h i) (P.nonneg i j)))

omit [DecidableEq S] in
theorem advance_mass (v : S → ℝ) (A : Finset S) :
    mass (P.advance v) A = ∑ i, v i * ∑ j ∈ A, P.prob i j := by
  unfold mass advance
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]

theorem advance_mass_lower {v : S → ℝ} (hv : ∀ i, 0 ≤ v i) (A : Finset S) :
    mass v A - P.outflow v A ≤ mass (P.advance v) A := by
  have hrow (i : S) : (∑ j ∈ A, P.prob i j) = 1 - ∑ j ∈ Aᶜ, P.prob i j := by
    have hh := (Finset.sum_add_sum_compl A (P.prob i)).trans (P.sum_one i)
    linarith
  rw [P.advance_mass]
  calc
    _ = ∑ i ∈ A, v i * ∑ j ∈ A, P.prob i j := by
      simp only [hrow, mul_sub, mul_one, Finset.sum_sub_distrib, mass, outflow]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun i _ _ => mul_nonneg (hv i) (Finset.sum_nonneg (fun j _ => P.nonneg i j)))

theorem evolve_mass_lower {v π : S → ℝ} {c : ℝ}
    (hv : v ∈ stdSimplex ℝ S) (hπ : P.StationaryVector π)
    (hdom : ∀ i, v i ≤ c * π i) (A : Finset S) (m : Nat) :
    mass v A - m * c * P.outflow π A ≤ mass (P.evolve m v) A := by
  induction m with
  | zero => simp [evolve]
  | succ m ih =>
    have hstep := P.advance_mass_lower (P.evolve_simplex hv m).1 A
    have hflow := P.outflow_dominated (P.evolve_dominated hπ hdom m) A
    change _ ≤ mass (P.advance (P.evolve m v)) A
    push_cast
    nlinarith

def condition (π : S → ℝ) (A : Finset S) (i : S) : ℝ := if i ∈ A then π i / mass π A else 0

omit P in
theorem condition_simplex {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S)
    (A : Finset S) (hA : 0 < mass π A) : condition π A ∈ stdSimplex ℝ S := by
  constructor
  · intro i
    unfold condition
    split_ifs
    · exact div_nonneg (hπ.1 i) hA.le
    · exact le_rfl
  · simp only [condition, Finset.sum_ite_mem, Finset.univ_inter, div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hA.ne'

omit P [Fintype S] in
theorem condition_mass {π : S → ℝ} (A : Finset S) (hA : 0 < mass π A) :
    mass (condition π A) A = 1 := by
  simp only [mass, condition, Finset.sum_ite_mem, Finset.inter_self, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ hA.ne'

omit P in
theorem condition_dominated {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S)
    (A : Finset S) (hA : 0 < mass π A) : ∀ i, condition π A i ≤ (mass π A)⁻¹ * π i := by
  intro i
  unfold condition
  split_ifs
  · exact le_of_eq (by rw [div_eq_mul_inv, mul_comm])
  · exact mul_nonneg (inv_nonneg.mpr hA.le) (hπ.1 i)

theorem bottleneck_lower {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S)
    (hstat : P.StationaryVector π) (A : Finset S) (hA : 0 < mass π A) (m : Nat) :
    1 - mass π A - m * (mass π A)⁻¹ * P.outflow π A ≤
      totalVariation (P.evolve m (condition π A)) π := by
  have hc := condition_simplex hπ A hA
  have hmass := P.evolve_mass_lower hc hstat (condition_dominated hπ A hA) A m
  rw [condition_mass A hA] at hmass
  have htv := mass_sub_le_totalVariation ((P.evolve_simplex hc m).2.trans hπ.2.symm) A
  linarith

theorem half_bottleneck_lower {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S)
    (hstat : P.StationaryVector π) (A : Finset S) (hA : mass π A = 1 / 2) (m : Nat) :
    1 / 2 - 2 * m * P.outflow π A ≤ totalVariation (P.evolve m (condition π A)) π := by
  have hh := P.bottleneck_lower hπ hstat A (by rw [hA]; norm_num) m
  rw [hA] at hh
  norm_num at hh
  linarith

end OddCycle.FiniteMarkov
