import OddCycle.FiniteStationary
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

/-! Existence of a finite stationary probability vector by Cesaro averages. -/

namespace OddCycle.FiniteMarkov

open Filter Topology

variable {S : Type*} [Fintype S] (P : FiniteMarkov S)

def distribution (v : S → ℝ) : Nat → S → ℝ
  | 0 => v
  | n + 1 => P.advance (distribution v n)

theorem distribution_simplex {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (n : Nat) :
    P.distribution v n ∈ stdSimplex ℝ S := by
  induction n with
  | zero => exact hv
  | succ n ih => exact P.advance_simplex ih

noncomputable def average (v : S → ℝ) (n : Nat) (j : S) : ℝ :=
  (1 / (n + 1 : Nat)) * ∑ k ∈ Finset.range (n + 1), P.distribution v k j

theorem average_simplex {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (n : Nat) :
    P.average v n ∈ stdSimplex ℝ S := by
  constructor
  · intro j
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun k _ => (P.distribution_simplex hv k).1 j
  · unfold average
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [(P.distribution_simplex hv _).2, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact one_div_mul_cancel (by exact_mod_cast (show n + 1 ≠ 0 by omega))

theorem advance_average (v : S → ℝ) (n : Nat) (j : S) :
    P.advance (P.average v n) j =
      (1 / (n + 1 : Nat)) * ∑ k ∈ Finset.range (n + 1), P.distribution v (k + 1) j := by
  unfold advance average
  simp only [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem average_defect (v : S → ℝ) (n : Nat) (j : S) :
    P.advance (P.average v n) j - P.average v n j =
      (1 / (n + 1 : Nat)) * (P.distribution v (n + 1) j - v j) := by
  rw [P.advance_average]
  unfold average
  rw [← mul_sub, ← Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun k => P.distribution v k j)]
  rfl

theorem average_defect_bound {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (n : Nat) (j : S) :
    |P.advance (P.average v n) j - P.average v n j| ≤ 1 / (n + 1 : Nat) := by
  rw [P.average_defect, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n + 1 : Nat))]
  have hx := mem_Icc_of_mem_stdSimplex (P.distribution_simplex hv (n + 1)) j
  have hy := mem_Icc_of_mem_stdSimplex hv j
  have he : |P.distribution v (n + 1) j - v j| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 1 / (n + 1 : Nat))

theorem average_defect_tendsto {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (j : S) :
    Tendsto (fun n => P.advance (P.average v n) j - P.average v n j) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero (fun n => abs_nonneg _) (fun n => P.average_defect_bound hv n j)
  simpa only [Nat.cast_add, Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : Nat => (1 : ℝ) / (n + 1)) atTop (𝓝 0))

theorem advance_tendsto {v : Nat → S → ℝ} {x : S → ℝ}
    (h : Tendsto v atTop (𝓝 x)) (j : S) :
    Tendsto (fun n => P.advance (v n) j) atTop (𝓝 (P.advance x j)) := by
  exact tendsto_finset_sum _ fun i _ => (tendsto_pi_nhds.mp h i).mul tendsto_const_nhds

/-- Every finite stochastic matrix on a nonempty state space has a
stationary probability vector. -/
theorem stationary_exists [Nonempty S] :
    ∃ v ∈ stdSimplex ℝ S, P.StationaryVector v := by
  classical
  let v : S → ℝ := Pi.single (Classical.arbitrary S) 1
  have hv : v ∈ stdSimplex ℝ S := single_mem_stdSimplex _ _
  obtain ⟨x, hx, f, hf, hlim⟩ := (isCompact_stdSimplex S).isSeqCompact.subseq_of_frequently_in
    (Frequently.of_forall (P.average_simplex hv))
  refine ⟨x, hx, fun j => ?_⟩
  have hdiff := (P.advance_tendsto hlim j).sub (tendsto_pi_nhds.mp hlim j)
  have hzero := (P.average_defect_tendsto hv j).comp hf.tendsto_atTop
  exact sub_eq_zero.mp (tendsto_nhds_unique hdiff hzero)

theorem stationary_exists_unique [Nonempty S] (hirr : P.Irreducible) :
    ∃! v : S → ℝ, v ∈ stdSimplex ℝ S ∧ P.StationaryVector v := by
  obtain ⟨v, hv, hs⟩ := P.stationary_exists
  exact ⟨v, ⟨hv, hs⟩, fun x hx => P.stationary_unique hirr hx.1 hv hx.2 hs⟩

end OddCycle.FiniteMarkov
