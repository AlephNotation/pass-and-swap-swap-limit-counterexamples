import OddCycle.ClockedPath
import OddCycle.MarkovPathReturn

/-! A probability measure on continuous-time jump paths: the embedded chain
and independent unit exponentials, divided by the state's total service rate.
The clock is nonexplosive and visits and returns are exactly preserved. -/

namespace OddCycle.FiniteMarkov

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable (P : FiniteMarkov S)

abbrev TimedSample (S : Type*) := (Nat → S) × ExponentialClock.Clock

noncomputable def timedLaw (s : S) : Measure (TimedSample S) := (P.pathMeasure s).prod ExponentialClock.law

instance timedLaw_probability (s : S) : IsProbabilityMeasure (P.timedLaw s) := by
  unfold timedLaw
  infer_instance

variable (rate : S → ℝ) (positive : ∀ s, 0 < rate s)

noncomputable def timedState (ω : TimedSample S) (t : ℝ≥0) : S :=
  ClockedPath.state rate positive ω.1 ω.2 t

noncomputable def eventTime (ω : TimedSample S) (n : Nat) : ℝ := ClockedPath.arrival rate ω.1 ω.2 n

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
include positive in
theorem eventTime_nonexplosive (ω : TimedSample S) : Tendsto (eventTime rate ω) atTop atTop :=
  ClockedPath.arrival_diverges rate positive ω.1 ω.2

def continuousHit (A : S → Prop) : Set (TimedSample S) := {ω | ∃ t, A (timedState rate positive ω t)}

def continuousReturn (s : S) : Set (TimedSample S) :=
  {ω | ∃ t : ℝ≥0, eventTime rate ω 1 ≤ t ∧ timedState rate positive ω t = s}

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem continuousHit_eq (A : S → Prop) : continuousHit rate positive A = {y | ∃ n, A (y n)} ×ˢ Set.univ := by
  ext ω
  exact (ClockedPath.visits_iff rate positive ω.1 ω.2 A).trans (by simp)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem continuousReturn_eq (s : S) : continuousReturn rate positive s = returnEvent s ×ˢ Set.univ := by
  ext ω
  exact (ClockedPath.returns_iff rate positive ω.1 ω.2 s).trans (by simp [returnEvent])

theorem continuousHit_measurable (A : S → Prop) : MeasurableSet (continuousHit rate positive A) := by
  rw [continuousHit_eq]
  apply MeasurableSet.prod _ MeasurableSet.univ
  simp only [setOf_exists]
  exact MeasurableSet.iUnion (fun n => (measurable_pi_apply (X := fun _ : Nat => S) n) (Set.to_countable {s | A s}).measurableSet)

theorem continuousReturn_measurable (s : S) : MeasurableSet (continuousReturn rate positive s) := by
  rw [continuousReturn_eq]
  exact (returnEvent_measurable s).prod MeasurableSet.univ

theorem continuousHit_probability (s : S) (A : S → Prop) :
    P.timedLaw s (continuousHit rate positive A) = P.pathMeasure s {y | ∃ n, A (y n)} := by
  rw [continuousHit_eq, timedLaw, Measure.prod_prod, measure_univ, mul_one]

theorem continuousReturn_probability (s : S) :
    P.timedLaw s (continuousReturn rate positive s) = P.pathMeasure s (returnEvent s) := by
  rw [continuousReturn_eq, timedLaw, Measure.prod_prod, measure_univ, mul_one]

theorem continuous_absorption (s : S) (A : S → Prop) [DecidablePred A]
    (h : Tendsto (fun m => P.avoidSet A m s) atTop (𝓝 0)) :
    P.timedLaw s (continuousHit rate positive A) = 1 := by
  rw [continuousHit_probability]
  exact P.pathMeasure_ever_hit A s h

variable [DecidableEq S]

theorem continuous_recurrence_iff (s : S) :
    P.timedLaw s (continuousReturn rate positive s) = 1 ↔ Tendsto (P.returnBy s) atTop (𝓝 1) := by
  rw [continuousReturn_probability, P.pathMeasure_return_iff]

end OddCycle.FiniteMarkov
