import OddCycle.MarkovPathHitting

namespace OddCycle.FiniteMarkov

open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped ENNReal Topology

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable (P : FiniteMarkov S)

theorem pathMeasure_nextAvoid (A : S → Prop) [DecidablePred A] (s : S) (m : Nat) :
    P.pathMeasure s (futureAvoid A 1 m) = ENNReal.ofReal (P.expect (P.avoidSet A m) s) := by
  rw [pathMeasure, P.pathMeasureFrom_step _ (futureAvoid_measurable A 1 m)]
  simp only [P.pathMeasureFrom_avoid A, extendPrefix_last, expect]
  rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg (P.nonneg s t) (P.avoidSet_nonneg A m t))]
  apply Finset.sum_congr rfl
  intro t _
  rw [ENNReal.ofReal_mul (P.nonneg s t)]

variable [DecidableEq S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem avoidSet_singleton (s : S) (m : Nat) : P.avoidSet (fun t => t = s) m = P.avoid s m := by
  induction m with
  | zero => rfl
  | succ m ih => funext t; simp only [avoidSet, avoid, ih]

def returnEvent (s : S) : Set (Nat → S) := {y | ∃ n, 1 ≤ n ∧ y n = s}

omit [Fintype S] [DecidableEq S] in
theorem returnEvent_measurable (s : S) : MeasurableSet (returnEvent s) := by
  simp only [returnEvent, setOf_exists]
  exact MeasurableSet.iUnion (fun n => (MeasurableSet.const (1 ≤ n)).inter
    (by simpa only [Set.preimage, Set.mem_singleton_iff] using (measurable_pi_apply (X := fun _ : Nat => S) n) (measurableSet_singleton s)))

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq S] in
theorem returnEvent_compl (s : S) :
    returnEvent s = (⋂ m, futureAvoid (fun t => t = s) 1 m)ᶜ := by
  rw [futureAvoid_inter]
  ext y
  simp only [returnEvent, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, Classical.not_not]
  constructor
  · rintro ⟨n, hn, hy⟩
    exact ⟨n - 1, by simpa only [show 1 + (n - 1) = n by omega] using hy⟩
  · rintro ⟨j, hj⟩
    exact ⟨1 + j, by omega, hj⟩

/-- Probability-one return on the constructed path space is equivalent to
convergence of the original finite-step return probabilities. -/
theorem pathMeasure_return_iff (s : S) :
    P.pathMeasure s (returnEvent s) = 1 ↔ Tendsto (P.returnBy s) atTop (𝓝 1) := by
  have hlim := tendsto_measure_iInter_atTop
    (fun m => (futureAvoid_measurable (fun t => t = s) 1 m).nullMeasurableSet)
    (futureAvoid_antitone (fun t => t = s) 1)
    (⟨0, measure_ne_top _ _⟩ : ∃ m, P.pathMeasure s (futureAvoid (fun t => t = s) 1 m) ≠ ∞)
  simp only [Function.comp_def, P.pathMeasure_nextAvoid, P.avoidSet_singleton] at hlim
  have hid (m : Nat) : P.expect (P.avoid s m) s = 1 - P.returnBy s m := by simp [returnBy]
  simp only [hid] at hlim
  rw [returnEvent_compl, prob_compl_eq_one_iff (MeasurableSet.iInter (futureAvoid_measurable (fun t => t = s) 1))]
  constructor
  · intro hz
    rw [hz] at hlim
    have hr : Tendsto (fun m => 1 - P.returnBy s m) atTop (𝓝 0) := by
      have hh := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
      simpa only [Function.comp_def, ENNReal.toReal_ofReal (sub_nonneg.mpr (P.returnBy_le_one s _)), ENNReal.toReal_zero] using hh
    have hh := tendsto_const_nhds.sub hr (a := (1 : ℝ))
    simpa only [sub_sub_cancel, sub_zero] using hh
  · intro hr
    have hh : Tendsto (fun m => ENNReal.ofReal (1 - P.returnBy s m)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, sub_self, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((tendsto_const_nhds (x := (1 : ℝ))).sub hr)
    exact tendsto_nhds_unique hlim hh

end OddCycle.FiniteMarkov
