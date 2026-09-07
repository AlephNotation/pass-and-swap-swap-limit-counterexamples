import OddCycle.FiniteMarkov
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic.FieldSimp

/-! Positivity and uniqueness of stationary probability vectors. -/

namespace OddCycle.FiniteMarkov

variable {S : Type*} [Fintype S] (P : FiniteMarkov S)

def advance (v : S → ℝ) (j : S) : ℝ := ∑ i, v i * P.prob i j

def StationaryVector (v : S → ℝ) : Prop := ∀ j, P.advance v j = v j

theorem advance_nonneg {v : S → ℝ} (hv : ∀ i, 0 ≤ v i) (j : S) : 0 ≤ P.advance v j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hv i) (P.nonneg i j)

theorem advance_sum (v : S → ℝ) : ∑ j, P.advance v j = ∑ j, v j := by
  unfold advance
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, P.sum_one, mul_one]

theorem advance_simplex {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) :
    P.advance v ∈ stdSimplex ℝ S :=
  ⟨P.advance_nonneg hv.1, (P.advance_sum v).trans hv.2⟩

theorem stationary_positive_step {v : S → ℝ} (hv : ∀ i, 0 ≤ v i) (hs : P.StationaryVector v)
    {i j : S} (hi : 0 < v i) (hij : 0 < P.prob i j) : 0 < v j := by
  rw [← hs j]
  exact lt_of_lt_of_le (mul_pos hi hij)
    (Finset.single_le_sum (fun k _ => mul_nonneg (hv k) (P.nonneg k j)) (Finset.mem_univ i))

theorem stationary_positive_reachable {v : S → ℝ} (hv : ∀ i, 0 ≤ v i)
    (hs : P.StationaryVector v) {i j : S} (hi : 0 < v i) (hr : P.Reachable i j) : 0 < v j := by
  induction hr with
  | refl => exact hi
  | tail _ hstep ih => exact P.stationary_positive_step hv hs ih hstep

theorem stationary_positive (hirr : P.Irreducible) {v : S → ℝ}
    (hv : v ∈ stdSimplex ℝ S) (hs : P.StationaryVector v) (j : S) : 0 < v j := by
  have hex : ∃ i, 0 < v i := by
    by_contra h
    have hz : ∀ i, v i = 0 := by
      intro i
      exact le_antisymm (le_of_not_gt (fun hi => h ⟨i, hi⟩)) (hv.1 i)
    have he := hv.2
    simp only [hz, Finset.sum_const_zero] at he
    exact zero_ne_one he
  obtain ⟨i, hi⟩ := hex
  exact P.stationary_positive_reachable hv.1 hs hi (hirr i j)

theorem stationary_boundary_zero (target : S) (hreach : ∀ i, P.Reachable i target)
    {v : S → ℝ} (hv : ∀ i, 0 ≤ v i) (hs : P.StationaryVector v) (hz : v target = 0) :
    ∀ i, v i = 0 := by
  intro i
  apply le_antisymm _ (hv i)
  by_contra h
  have hp := P.stationary_positive_reachable hv hs (lt_of_not_ge h) (hreach i)
  rw [hz] at hp
  exact (lt_irrefl 0) hp

theorem advance_sub_scale (x y : S → ℝ) (a : ℝ) (j : S) :
    P.advance (fun i => x i - a * y i) j = P.advance x j - a * P.advance y j := by
  simp only [advance, sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]

theorem stationary_unique [Nonempty S] (hirr : P.Irreducible) {x y : S → ℝ}
    (hx : x ∈ stdSimplex ℝ S) (hy : y ∈ stdSimplex ℝ S)
    (hsx : P.StationaryVector x) (hsy : P.StationaryVector y) : x = y := by
  have hyp : ∀ i, 0 < y i := P.stationary_positive hirr hy hsy
  obtain ⟨m, _, hm⟩ := Finset.exists_min_image Finset.univ (fun i => x i / y i) Finset.univ_nonempty
  let a := x m / y m
  have hn : ∀ i, 0 ≤ x i - a * y i := by
    intro i
    apply sub_nonneg.mpr
    exact (le_div_iff₀ (hyp i)).mp (hm i (Finset.mem_univ i))
  have hfixed : P.StationaryVector (fun i => x i - a * y i) := by
    intro j
    rw [P.advance_sub_scale, hsx j, hsy j]
  have hzero : x m - a * y m = 0 := by rw [div_mul_cancel₀ _ (hyp m).ne', sub_self]
  have he := P.stationary_boundary_zero m (fun i => hirr i m) hn hfixed hzero
  have hxy : ∀ i, x i = a * y i := fun i => sub_eq_zero.mp (he i)
  have ha : a = 1 := by
    have hsum := hx.2
    simp only [hxy, ← Finset.mul_sum, hy.2, mul_one] at hsum
    exact hsum
  funext i
  simpa only [ha, one_mul] using hxy i

end OddCycle.FiniteMarkov
