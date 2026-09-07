import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith

/-! Finite stochastic transition matrices and their maximum principle. -/

namespace OddCycle

structure FiniteMarkov (S : Type*) [Fintype S] where
  prob : S → S → ℝ
  nonneg : ∀ i j, 0 ≤ prob i j
  sum_one : ∀ i, ∑ j, prob i j = 1

namespace FiniteMarkov

variable {S : Type*} [Fintype S] (P : FiniteMarkov S)

def expect (f : S → ℝ) (i : S) : ℝ := ∑ j, P.prob i j * f j

def Reachable (i j : S) : Prop := Relation.ReflTransGen (fun a b => 0 < P.prob a b) i j

def Irreducible : Prop := ∀ i j, P.Reachable i j

theorem expect_const (a : ℝ) (i : S) : P.expect (fun _ => a) i = a := by
  simp only [expect, ← Finset.sum_mul, P.sum_one, one_mul]

theorem expect_mono {f g : S → ℝ} (h : ∀ j, f j ≤ g j) (i : S) : P.expect f i ≤ P.expect g i :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (P.nonneg i j)

theorem expect_nonneg {f : S → ℝ} (h : ∀ j, 0 ≤ f j) (i : S) : 0 ≤ P.expect f i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (P.nonneg i j) (h j)

theorem expect_sub (f g : S → ℝ) (i : S) :
    P.expect (fun j => f j - g j) i = P.expect f i - P.expect g i := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

/-- A stochastic average can attain its global maximum only when every
positive-probability successor attains the same maximum. -/
theorem maximum_step {f : S → ℝ} {i j : S} (hm : ∀ k, f k ≤ f i)
    (he : P.expect f i = f i) (hp : 0 < P.prob i j) : f j = f i := by
  have hn : ∀ k, 0 ≤ P.prob i k * (f i - f k) :=
    fun k => mul_nonneg (P.nonneg i k) (sub_nonneg.mpr (hm k))
  have hz : ∑ k, P.prob i k * (f i - f k) = 0 := by
    change P.expect (fun k => f i - f k) i = 0
    rw [P.expect_sub, P.expect_const, he, sub_self]
  have hj : P.prob i j * (f i - f j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hn k)).mp hz j (Finset.mem_univ j)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hj).resolve_left hp.ne')).symm

theorem harmonic_constant [Nonempty S] (hirr : P.Irreducible) {f : S → ℝ}
    (hf : ∀ i, P.expect f i = f i) : ∀ i j, f i = f j := by
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have hmax : ∀ i, f i ≤ f m := fun i => hm i (Finset.mem_univ i)
  have hall : ∀ j, f j = f m := by
    intro j
    have hr := hirr m j
    induction hr with
    | refl => rfl
    | @tail b c _ hbc ih =>
      have h := P.maximum_step (fun k => by rw [ih]; exact hmax k) (hf b) hbc
      exact h.trans ih
  exact fun i j => (hall i).trans (hall j).symm

/-- An absorbing boundary value zero forces every nonnegative harmonic
function off that boundary to vanish when every state can reach it. -/
theorem harmonic_boundary_zero (target : S) (hreach : ∀ i, P.Reachable i target)
    {f : S → ℝ} (hn : ∀ i, 0 ≤ f i) (hz : f target = 0)
    (hf : ∀ i, i ≠ target → P.expect f i = f i) : ∀ i, f i = 0 := by
  letI : Nonempty S := ⟨target⟩
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have hmax : ∀ i, f i ≤ f m := fun i => hm i (Finset.mem_univ i)
  have hle : f m ≤ 0 := by
    by_contra h
    have hp : 0 < f m := lt_of_not_ge h
    have hall : ∀ j, P.Reachable m j → f j = f m := by
      intro j hr
      induction hr with
      | refl => rfl
      | @tail b c _ hbc ih =>
        have hb : b ≠ target := by intro he; rw [he, hz] at ih; exact hp.ne' ih.symm
        exact (P.maximum_step (fun k => by rw [ih]; exact hmax k) (hf b hb) hbc).trans ih
    have hend := hall target (hreach m)
    rw [hz] at hend
    exact hp.ne' hend.symm
  exact fun i => le_antisymm ((hmax i).trans hle) (hn i)

end FiniteMarkov
end OddCycle
