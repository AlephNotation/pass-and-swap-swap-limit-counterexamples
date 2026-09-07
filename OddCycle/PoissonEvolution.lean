import OddCycle.FiniteBottleneck
import Mathlib.Probability.Distributions.Poisson

/-! Poisson averaging of finite completion-kernel laws. The bounds here are
proved for this explicit series; its identification with the existing
exponential-clocked sample-path construction is a separate obligation. -/

noncomputable section

namespace OddCycle.FiniteMarkov

open ProbabilityTheory Finset
open scoped NNReal

theorem poisson_first_moment (r : ℝ≥0) : HasSum (fun m => poissonPMFReal r m * m) (r : ℝ) := by
  have hrec (m : Nat) : poissonPMFReal r (m + 1) * (m + 1) = (r : ℝ) * poissonPMFReal r m := by
    unfold poissonPMFReal
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    push_cast
    field_simp
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Nat.cast_add, Nat.cast_one, hrec, Finset.sum_range_one, Nat.cast_zero, mul_zero, sub_zero, mul_one] using
    (poissonPMFRealSum r).mul_left (r : ℝ)

theorem poisson_affine_sum (r : ℝ≥0) (a b : ℝ) :
    HasSum (fun m => poissonPMFReal r m * (a - m * b)) (a - r * b) := by
  have h := ((poissonPMFRealSum r).mul_right a).sub ((poisson_first_moment r).mul_right b)
  simpa only [mul_sub, mul_assoc, one_mul] using h

variable {S : Type*} [Fintype S] (P : FiniteMarkov S)

def poissonEvolve (r : ℝ≥0) (v : S → ℝ) (j : S) : ℝ :=
  ∑' m, poissonPMFReal r m * P.evolve m v j

theorem poisson_component_summable {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (r : ℝ≥0) (j : S) :
    Summable (fun m => poissonPMFReal r m * P.evolve m v j) := by
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg poissonPMFReal_nonneg ((P.evolve_simplex hv m).1 j)) _
    (poissonPMFRealSum r).summable
  intro m
  have h := (P.evolve_simplex hv m)
  have hj : P.evolve m v j ≤ 1 := by
    rw [← h.2]
    exact Finset.single_le_sum (fun i _ => h.1 i) (Finset.mem_univ j)
  exact (mul_le_mul_of_nonneg_left hj poissonPMFReal_nonneg).trans_eq (mul_one _)

theorem poissonEvolve_simplex {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (r : ℝ≥0) :
    P.poissonEvolve r v ∈ stdSimplex ℝ S := by
  constructor
  · intro j
    exact tsum_nonneg (fun m => mul_nonneg poissonPMFReal_nonneg ((P.evolve_simplex hv m).1 j))
  · unfold poissonEvolve
    rw [← Summable.tsum_finsetSum (fun j _ => P.poisson_component_summable hv r j)]
    simp only [← Finset.mul_sum, (P.evolve_simplex hv _).2, mul_one]
    exact (poissonPMFRealSum r).tsum_eq

theorem poissonEvolve_stationary {π : S → ℝ} (hπ : P.StationaryVector π) (r : ℝ≥0) :
    P.poissonEvolve r π = π := by
  funext j
  simp only [poissonEvolve, P.evolve_stationary hπ, tsum_mul_right, (poissonPMFRealSum r).tsum_eq, one_mul]

theorem poissonEvolve_mass {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (r : ℝ≥0) (A : Finset S) :
    mass (P.poissonEvolve r v) A = ∑' m, poissonPMFReal r m * mass (P.evolve m v) A := by
  unfold mass poissonEvolve
  rw [← Summable.tsum_finsetSum (fun j _ => P.poisson_component_summable hv r j)]
  simp only [← Finset.mul_sum]

theorem poisson_mass_summable {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (r : ℝ≥0) (A : Finset S) :
    Summable (fun m => poissonPMFReal r m * mass (P.evolve m v) A) := by
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg poissonPMFReal_nonneg (mass_nonneg (P.evolve_simplex hv m).1 A)) _
    (poissonPMFRealSum r).summable
  intro m
  exact (mul_le_mul_of_nonneg_left (mass_le_one (P.evolve_simplex hv m) A) poissonPMFReal_nonneg).trans_eq (mul_one _)

variable [DecidableEq S]

theorem poisson_bottleneck_lower {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S)
    (hstat : P.StationaryVector π) (A : Finset S) (hA : 0 < mass π A) (r : ℝ≥0) :
    1 - mass π A - r * (mass π A)⁻¹ * P.outflow π A ≤
      totalVariation (P.poissonEvolve r (condition π A)) π := by
  have hc := condition_simplex hπ A hA
  have hbound (m : Nat) : poissonPMFReal r m * (1 - m * ((mass π A)⁻¹ * P.outflow π A)) ≤
      poissonPMFReal r m * mass (P.evolve m (condition π A)) A := by
    have hh := P.evolve_mass_lower hc hstat (condition_dominated hπ A hA) A m
    rw [condition_mass A hA] at hh
    exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hh) poissonPMFReal_nonneg
  have hs := poisson_affine_sum r 1 ((mass π A)⁻¹ * P.outflow π A)
  have hmass := Summable.tsum_le_tsum hbound hs.summable (P.poisson_mass_summable hc r A)
  rw [hs.tsum_eq, ← P.poissonEvolve_mass hc r A] at hmass
  have htv := mass_sub_le_totalVariation ((P.poissonEvolve_simplex hc r).2.trans hπ.2.symm) A
  nlinarith

theorem poisson_half_bottleneck_lower {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S)
    (hstat : P.StationaryVector π) (A : Finset S) (hA : mass π A = 1 / 2) (r : ℝ≥0) :
    1 / 2 - 2 * r * P.outflow π A ≤ totalVariation (P.poissonEvolve r (condition π A)) π := by
  have hh := P.poisson_bottleneck_lower hπ hstat A (by rw [hA]; norm_num) r
  rw [hA] at hh
  norm_num at hh
  linarith

end OddCycle.FiniteMarkov
