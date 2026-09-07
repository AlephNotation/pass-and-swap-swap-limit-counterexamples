import OddCycle.FiniteRecurrence

/-! Return probabilities inside an arbitrary nonempty finite closed set. -/

namespace OddCycle.FiniteMarkov

open Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] (P : FiniteMarkov S)
variable (A : S → Prop) [DecidablePred A]
variable (hc : ∀ i, A i → ∀ j, ¬ A j → P.prob i j = 0)

omit [DecidableEq S] in
include hc in
theorem closed_sum (i : {s // A s}) (f : S → ℝ) :
    (∑ j : {s // A s}, P.prob i.val j.val * f j.val) = P.expect f i.val := by
  rw [← Finset.sum_subtype (Finset.univ.filter A) (by simp) (fun j => P.prob i.val j * f j)]
  rw [Finset.sum_filter]
  unfold expect
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : A j
  · simp only [if_pos hj]
  · simp only [if_neg hj, hc i.val i.property j hj, zero_mul]

noncomputable def restrict : FiniteMarkov {s // A s} where
  prob i j := P.prob i.val j.val
  nonneg i j := P.nonneg i.val j.val
  sum_one i := by
    have h := P.closed_sum A hc i (fun _ => 1)
    simpa only [mul_one, P.expect_const] using h

theorem restrict_avoid (target : {s // A s}) (n : Nat) (i : {s // A s}) :
    (P.restrict A hc).avoid target n i = P.avoid target.val n i.val := by
  induction n generalizing i with
  | zero => simp only [avoid, Subtype.ext_iff]
  | succ n ih =>
    simp only [avoid, Subtype.ext_iff]
    split_ifs with he
    · rfl
    · change (∑ j : {s // A s}, P.prob i.val j.val * (P.restrict A hc).avoid target n j) = _
      simp_rw [ih]
      exact P.closed_sum A hc i (P.avoid target.val n)

theorem restrict_returnBy (target : {s // A s}) (n : Nat) :
    (P.restrict A hc).returnBy target n = P.returnBy target.val n := by
  unfold returnBy
  congr 1
  change (∑ j : {s // A s}, P.prob target.val j.val * (P.restrict A hc).avoid target n j) = _
  simp_rw [P.restrict_avoid A hc]
  exact P.closed_sum A hc target (P.avoid target.val n)

include hc in
/-- A nonempty closed set in a finite chain contains a state whose
positive-time return probability tends to one in the original chain. -/
theorem closed_recurrent_state_exists (hne : ∃ i, A i) :
    ∃ target, A target ∧ Tendsto (P.returnBy target) atTop (𝓝 1) := by
  letI : Nonempty {s // A s} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨target, ht⟩ := (P.restrict A hc).recurrent_state_exists
  refine ⟨target.val, target.property, ?_⟩
  have he : (P.restrict A hc).returnBy target = P.returnBy target.val := by
    funext n
    exact P.restrict_returnBy A hc target n
  rwa [he] at ht

end OddCycle.FiniteMarkov
