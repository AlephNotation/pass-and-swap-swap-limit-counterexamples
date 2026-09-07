import OddCycle.CompletionMarginals

/-! A stationary completion law remains stationary at every real time when
the total event rate is constant. The proof conditions on the existing clock;
it does not assume a Poisson representation. -/

noncomputable section

namespace OddCycle.FiniteMarkov

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable (P : FiniteMarkov S)

theorem constantRate_stationary_current (rate : ℝ) (hr : 0 < rate)
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (hstat : P.StationaryVector π) (t : ℝ≥0) (j : S) :
    P.mixedTimedLaw π {ω | timedState (fun _ => rate) (fun _ => hr) ω t = j} = ENNReal.ofReal (π j) := by
  letI := P.mixedPathLaw_probability hπ
  have hm : MeasurableSet {ω : TimedSample S | timedState (fun _ => rate) (fun _ => hr) ω t = j} :=
    (timedState_measurable (fun _ => rate) (fun _ => hr) t) (measurableSet_singleton j)
  rw [mixedTimedLaw, Measure.prod_apply_symm hm]
  change (∫⁻ z : ExponentialClock.Clock, P.mixedPathLaw π
    {y | y (ClockedPath.index (fun _ : S => rate) (fun _ => hr) (fun _ => Classical.arbitrary S) z t) = j}
    ∂ExponentialClock.law) = _
  simp_rw [P.mixedPathLaw_stationary_current hπ hstat]
  simp

end OddCycle.FiniteMarkov
