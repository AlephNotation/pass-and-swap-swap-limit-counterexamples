import OddCycle.RecurrenceClassification
import OddCycle.FiniteGraphSymmetry

/-! Finite chains eventually enter their terminal components with probability
one, expressed by the finite-horizon probability of avoiding a set. -/

namespace OddCycle.ReachabilityQuotient

theorem reachable_terminal {S : Type*} [Fintype S] (step : S → S → Prop) (x : S) :
    ∃ y, Reach step x y ∧ Terminal step y := by
  classical
  have hne : (reachableSet step x).Nonempty := ⟨x, (mem_reachableSet step x x).mpr .refl⟩
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image (reachableSet step x)
    (fun y => (reachableSet step y).card) hne
  have hxy := (mem_reachableSet step x y).mp hy
  refine ⟨y, hxy, fun z hyz => return_of_reachable_card_le step hyz ?_⟩
  exact hmin z ((mem_reachableSet step x z).mpr (hxy.trans hyz))

end OddCycle.ReachabilityQuotient

namespace OddCycle.FiniteMarkov

open Filter Topology

variable {S : Type*} [Fintype S] (P : FiniteMarkov S)
variable (A : S → Prop) [DecidablePred A]

def avoidSet : Nat → S → ℝ
  | 0, i => if A i then 0 else 1
  | n + 1, i => if A i then 0 else P.expect (avoidSet n) i

theorem avoidSet_mem {i : S} (hi : A i) (n : Nat) : P.avoidSet A n i = 0 := by
  cases n <;> simp [avoidSet, hi]

theorem avoidSet_nonneg (n : Nat) (i : S) : 0 ≤ P.avoidSet A n i := by
  induction n generalizing i with
  | zero => simp only [avoidSet]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [avoidSet]
    split_ifs
    · exact le_rfl
    · exact P.expect_nonneg ih i

theorem avoidSet_le_one (n : Nat) (i : S) : P.avoidSet A n i ≤ 1 := by
  induction n generalizing i with
  | zero => simp only [avoidSet]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [avoidSet]
    split_ifs
    · exact zero_le_one
    · simpa only [P.expect_const] using P.expect_mono ih i

theorem avoidSet_succ_le (n : Nat) (i : S) : P.avoidSet A (n + 1) i ≤ P.avoidSet A n i := by
  induction n generalizing i with
  | zero =>
    by_cases hi : A i
    · simp only [P.avoidSet_mem A hi, le_refl]
    · simpa only [avoidSet, if_neg hi] using P.avoidSet_le_one A 1 i
  | succ n ih =>
    simp only [avoidSet]
    split_ifs
    · exact le_rfl
    · exact P.expect_mono ih i

noncomputable def avoidSetLimit (i : S) : ℝ := ⨅ n, P.avoidSet A n i

theorem avoidSet_tendsto (i : S) :
    Tendsto (fun n => P.avoidSet A n i) atTop (𝓝 (P.avoidSetLimit A i)) :=
  tendsto_atTop_ciInf (antitone_nat_of_succ_le (fun n => P.avoidSet_succ_le A n i))
    ⟨0, by rintro _ ⟨n, rfl⟩; exact P.avoidSet_nonneg A n i⟩

theorem avoidSetLimit_harmonic (i : S) (hi : ¬ A i) :
    P.expect (P.avoidSetLimit A) i = P.avoidSetLimit A i := by
  have h := (P.avoidSet_tendsto A i).comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n => P.avoidSet A (n + 1) i) atTop _ at h
  simp only [avoidSet, if_neg hi] at h
  exact tendsto_nhds_unique (P.expect_tendsto (P.avoidSet_tendsto A) i) h

theorem avoidSetLimit_zero (hreach : ∀ i, ∃ j, A j ∧ P.Reachable i j) (i : S) :
    P.avoidSetLimit A i = 0 := by
  letI : Nonempty S := ⟨i⟩
  let f := P.avoidSetLimit A
  have hn (j : S) : 0 ≤ f j := le_ciInf (fun n => P.avoidSet_nonneg A n j)
  have hz (j : S) (hj : A j) : f j = 0 := by simp [f, avoidSetLimit, P.avoidSet_mem A hj]
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have hmax (j : S) : f j ≤ f m := hm j (Finset.mem_univ j)
  have hle : f m ≤ 0 := by
    by_contra hh
    have hp : 0 < f m := lt_of_not_ge hh
    have hall : ∀ j, P.Reachable m j → f j = f m := by
      intro j hr
      induction hr with
      | refl => rfl
      | @tail j k hr hjk ih =>
        have hj : ¬ A j := by intro hj; have := hz j hj; rw [ih] at this; linarith
        exact (P.maximum_step (fun k => by change f k ≤ f j; rw [ih]; exact hmax k)
          (P.avoidSetLimit_harmonic A j hj) hjk).trans ih
    obtain ⟨j, hj, hr⟩ := hreach m
    have he := hall j hr
    rw [hz j hj] at he
    exact hp.ne' he.symm
  exact le_antisymm ((hmax i).trans hle) (hn i)

theorem avoidSet_tendsto_zero (hreach : ∀ i, ∃ j, A j ∧ P.Reachable i j) (i : S) :
    Tendsto (fun n => P.avoidSet A n i) atTop (𝓝 0) := by
  simpa only [P.avoidSetLimit_zero A hreach] using P.avoidSet_tendsto A i

attribute [local instance] Classical.propDecidable

theorem avoid_terminal_tendsto_zero (i : S) :
    Tendsto (fun n => P.avoidSet
      (ReachabilityQuotient.Terminal (fun a b => 0 < P.prob a b)) n i) atTop (𝓝 0) := by
  apply P.avoidSet_tendsto_zero
  intro j
  obtain ⟨k, hr, ht⟩ := ReachabilityQuotient.reachable_terminal (fun a b => 0 < P.prob a b) j
  exact ⟨k, ht, hr⟩

end OddCycle.FiniteMarkov
