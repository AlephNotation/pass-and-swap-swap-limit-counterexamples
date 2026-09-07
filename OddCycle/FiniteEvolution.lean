import OddCycle.FiniteStationary
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite-time laws and total variation for a finite completion kernel.
The distributions are ordinary probability vectors on the original state space. -/

noncomputable section

namespace OddCycle.FiniteMarkov

open Finset

variable {S : Type*} [Fintype S] (P : FiniteMarkov S)

def evolve : Nat → (S → ℝ) → S → ℝ
  | 0, v => v
  | m + 1, v => P.advance (evolve m v)

def mass (v : S → ℝ) (A : Finset S) : ℝ := ∑ i ∈ A, v i

def totalVariation (v u : S → ℝ) : ℝ := (∑ i, |v i - u i|) / 2

theorem advance_mono {v u : S → ℝ} (h : ∀ i, v i ≤ u i) (j : S) :
    P.advance v j ≤ P.advance u j :=
  Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h i) (P.nonneg i j))

theorem advance_scale (c : ℝ) (v : S → ℝ) (j : S) :
    P.advance (fun i => c * v i) j = c * P.advance v j := by
  simp only [advance, Finset.mul_sum, mul_assoc]

theorem evolve_simplex {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (m : Nat) :
    P.evolve m v ∈ stdSimplex ℝ S := by
  induction m with
  | zero => exact hv
  | succ m ih => exact P.advance_simplex ih

theorem evolve_stationary {π : S → ℝ} (hπ : P.StationaryVector π) (m : Nat) :
    P.evolve m π = π := by
  induction m with
  | zero => rfl
  | succ m ih => funext j; simp only [evolve, ih]; exact hπ j

theorem evolve_dominated {v π : S → ℝ} {c : ℝ}
    (hπ : P.StationaryVector π) (h : ∀ i, v i ≤ c * π i) (m : Nat) :
    ∀ i, P.evolve m v i ≤ c * π i := by
  induction m with
  | zero => exact h
  | succ m ih =>
    intro i
    exact (P.advance_mono ih i).trans_eq (by rw [P.advance_scale, hπ i])

omit P [Fintype S] in
theorem mass_nonneg {v : S → ℝ} (hv : ∀ i, 0 ≤ v i) (A : Finset S) : 0 ≤ mass v A :=
  Finset.sum_nonneg (fun i _ => hv i)

omit P in
theorem mass_le_one {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (A : Finset S) : mass v A ≤ 1 := by
  rw [← hv.2]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun i _ _ => hv.1 i)

omit P in
theorem totalVariation_nonneg (v u : S → ℝ) : 0 ≤ totalVariation v u := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

omit P in
theorem mass_sub_le_totalVariation {v u : S → ℝ}
    (he : ∑ i, v i = ∑ i, u i) (A : Finset S) : mass v A - mass u A ≤ totalVariation v u := by
  classical
  have hz : ∑ i, (v i - u i) = 0 := by rw [Finset.sum_sub_distrib, he, sub_self]
  have hsplit := Finset.sum_add_sum_compl A (fun i => v i - u i)
  have habs := Finset.sum_add_sum_compl A (fun i => |v i - u i|)
  have h₁ : (∑ i ∈ A, (v i - u i)) ≤ ∑ i ∈ A, |v i - u i| :=
    Finset.sum_le_sum (fun i _ => le_abs_self _)
  have h₂ : -(∑ i ∈ Aᶜ, (v i - u i)) ≤ ∑ i ∈ Aᶜ, |v i - u i| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i _ => neg_le_abs _)
  unfold mass totalVariation
  rw [← Finset.sum_sub_distrib]
  rw [hz] at hsplit
  linarith

variable [DecidableEq S]

def pointMass (i : S) (j : S) : ℝ := if j = i then 1 else 0

omit P in
theorem pointMass_simplex (i : S) : pointMass i ∈ stdSimplex ℝ S := by
  constructor
  · intro j; simp only [pointMass]; split_ifs <;> norm_num
  · simp [pointMass]

theorem evolve_mixture (v : S → ℝ) (m : Nat) (j : S) :
    P.evolve m v j = ∑ i, v i * P.evolve m (pointMass i) j := by
  induction m generalizing j with
  | zero => simp [evolve, pointMass]
  | succ m ih =>
    simp only [evolve, advance, ih, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem totalVariation_mixture {v π : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (m : Nat) :
    totalVariation (P.evolve m v) π ≤ ∑ i, v i * totalVariation (P.evolve m (pointMass i)) π := by
  have he (j : S) : P.evolve m v j - π j = ∑ i, v i * (P.evolve m (pointMass i) j - π j) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hv.2, one_mul, ← P.evolve_mixture]
  have hb (j : S) : |P.evolve m v j - π j| ≤ ∑ i, v i * |P.evolve m (pointMass i) j - π j| := by
    rw [he]
    calc
      _ ≤ ∑ i, |v i * (P.evolve m (pointMass i) j - π j)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, abs_of_nonneg (hv.1 _)]
  unfold totalVariation
  calc
    _ ≤ (∑ j, ∑ i, v i * |P.evolve m (pointMass i) j - π j|) / 2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _ => hb j)) (by norm_num)
    _ = _ := by rw [Finset.sum_comm]; simp only [← Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul, mul_assoc]

end OddCycle.FiniteMarkov
