import OddCycle.FiniteEvolution
import OddCycle.StationaryExistence

/-! Exact finite-kernel projections, defined by sums of the actual transition
probabilities over observation fibers. -/

noncomputable section

namespace OddCycle.FiniteMarkov

open Finset

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]

def push (f : S → T) (v : S → ℝ) (j : T) : ℝ := ∑ i, if f i = j then v i else 0

theorem sum_fibers {K : Type*} [CommSemiring K] (f : S → T) (v : S → K) (g : T → K) :
    (∑ i, v i * g (f i)) = ∑ j, (∑ i, if f i = j then v i else 0) * g j := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul]
  simp

theorem push_simplex (f : S → T) {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) :
    push f v ∈ stdSimplex ℝ T := by
  constructor
  · intro j; exact Finset.sum_nonneg (fun i _ => by split_ifs; exact hv.1 i; exact le_rfl)
  · have h := sum_fibers f v (fun _ => (1 : ℝ))
    simpa only [push, mul_one, hv.2] using h.symm

variable (P : FiniteMarkov S) (R : FiniteMarkov T) (f : S → T)

def LumpsTo : Prop := ∀ i j, push f (P.prob i) j = R.prob (f i) j

def project (representative : T → S) : FiniteMarkov T where
  prob i j := push f (P.prob (representative i)) j
  nonneg i j := (push_simplex f ⟨P.nonneg (representative i), P.sum_one (representative i)⟩).1 j
  sum_one i := (push_simplex f ⟨P.nonneg (representative i), P.sum_one (representative i)⟩).2

theorem lumps_project (representative : T → S) (hr : ∀ j, f (representative j) = j)
    (h : ∀ s t, f s = f t → push f (P.prob s) = push f (P.prob t)) :
    P.LumpsTo (P.project f representative) f := by
  intro s j
  exact congrFun (h s (representative (f s)) (hr _).symm) j

variable {P R f}

theorem LumpsTo.expect (h : P.LumpsTo R f) (g : T → ℝ) (i : S) :
    P.expect (g ∘ f) i = R.expect g (f i) := by
  have hh := sum_fibers f (P.prob i) g
  change _ = ∑ j, push f (P.prob i) j * g j at hh
  simpa only [FiniteMarkov.expect, h _ _, Function.comp_apply] using hh

theorem LumpsTo.push_advance (h : P.LumpsTo R f) (v : S → ℝ) :
    push f (P.advance v) = R.advance (push f v) := by
  funext j
  have hs (t : S) : (if f t = j then P.advance v t else 0) =
      ∑ i, v i * (if f t = j then P.prob i t else 0) := by
    split_ifs <;> simp only [advance, mul_zero, Finset.sum_const_zero]
  unfold push
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  change (∑ i, v i * push f (P.prob i) j) = _
  simp_rw [h _ _]
  exact sum_fibers f v (fun t => R.prob t j)

theorem LumpsTo.push_stationary (h : P.LumpsTo R f) {v : S → ℝ} (hv : P.StationaryVector v) :
    R.StationaryVector (push f v) := by
  intro j
  rw [← h.push_advance]
  change (∑ i, if f i = j then P.advance v i else 0) = _
  simp only [hv _, push]

theorem LumpsTo.step (h : P.LumpsTo R f) {i j : S} (hp : 0 < P.prob i j) :
    0 < R.prob (f i) (f j) := by
  rw [← h i (f j)]
  have hh : (if f j = f j then P.prob i j else 0) ≤ ∑ t, if f t = f j then P.prob i t else 0 := by
    apply Finset.single_le_sum (f := fun t => if f t = f j then P.prob i t else 0)
      (fun t _ => ?_) (Finset.mem_univ j)
    dsimp only
    split_ifs
    · exact P.nonneg i t
    · exact le_rfl
  exact hp.trans_le (by simpa only [if_true] using hh)

theorem LumpsTo.irreducible (h : P.LumpsTo R f) (hirr : P.Irreducible) (hf : Function.Surjective f) :
    R.Irreducible := by
  intro i j
  obtain ⟨s, rfl⟩ := hf i
  obtain ⟨t, rfl⟩ := hf j
  have hh := hirr s t
  induction hh with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (h.step hs)

omit [Fintype T] in
theorem push_defect_observable (P : FiniteMarkov S) (f : S → T) (v : S → ℝ) (j : T) :
    push f (P.advance v) j - push f v j =
      ∑ s, v s * (P.expect (fun t => if f t = j then 1 else 0) s -
        (if f s = j then 1 else 0)) := by
  unfold push advance expect
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  congr 1
  simp only [Finset.sum_ite, Finset.sum_const_zero]
  rw [Finset.sum_comm]
  simp only [add_zero]

theorem LumpsTo.stationary_of_observables (h : P.LumpsTo R f) {v : S → ℝ}
    (hv : ∀ g : T → ℝ, (∑ s, v s * (P.expect (g ∘ f) s - g (f s))) = 0) :
    R.StationaryVector (push f v) := by
  intro j
  have hh := hv (fun t => if t = j then 1 else 0)
  change (∑ s, v s * (P.expect (fun t => if f t = j then 1 else 0) s -
    (if f s = j then 1 else 0))) = 0 at hh
  rw [← push_defect_observable P f v j, h.push_advance] at hh
  exact sub_eq_zero.mp hh

end OddCycle.FiniteMarkov
