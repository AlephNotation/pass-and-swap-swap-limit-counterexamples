import OddCycle.TimedStateMeasurable
import OddCycle.MarkovPathSupport

/-! The first completion has the specified exponential rate and independent
destination law. The same construction is used after every finite history. -/

namespace OddCycle.FiniteMarkov

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable (P : FiniteMarkov S) (rate : S → ℝ) (positive : ∀ s, 0 < rate s)

theorem timedLaw_ae_initial (s : S) : ∀ᵐ ω ∂P.timedLaw s, ω.1 0 = s :=
  Measure.quasiMeasurePreserving_fst.ae (P.pathMeasureFrom_ae_current (a := 0) (fun _ => s))

theorem timedLaw_ae_steps (s : S) :
    ∀ᵐ ω ∂P.timedLaw s, ∀ n, 0 < P.prob (ω.1 n) (ω.1 (n + 1)) :=
  Measure.quasiMeasurePreserving_fst.ae (P.pathMeasure_ae_steps s)

theorem pathMeasure_next_singleton (s u : S) :
    P.pathMeasure s {y | y 1 = u} = ENNReal.ofReal (P.prob s u) := by
  have h := Measure.map_apply (measurable_pi_apply (X := fun _ : Nat => S) 1) (measurableSet_singleton u)
    (μ := P.pathMeasure s)
  have he := P.pathMeasureFrom_next (a := 0) (fun _ => s)
  change (P.pathMeasure s).map (fun y => y 1) = P.rowMeasure s at he
  rw [he, P.rowMeasure_singleton] at h
  exact h.symm

include positive in
theorem first_completion_law (s u : S) {t : ℝ} (ht : 0 ≤ t) :
    P.timedLaw s {ω | t < eventTime rate ω 1 ∧ ω.1 1 = u} =
      ENNReal.ofReal (Real.exp (-(rate s * t))) * ENNReal.ofReal (P.prob s u) := by
  have he : {ω : TimedSample S | t < eventTime rate ω 1 ∧ ω.1 1 = u} =ᵐ[P.timedLaw s]
      ({y | y 1 = u} ×ˢ {z : ExponentialClock.Clock | rate s * t < z.val 0}) := by
    filter_upwards [P.timedLaw_ae_initial s] with ω hω
    apply propext
    change (t < eventTime rate ω 1 ∧ ω.1 1 = u) ↔ (ω.1 1 = u ∧ rate s * t < ω.2.val 0)
    simp only [eventTime, ClockedPath.arrival, Finset.sum_range_one, hω]
    rw [lt_div_iff₀ (positive s), mul_comm t (rate s), and_comm]
  rw [measure_congr he, timedLaw, Measure.prod_prod, P.pathMeasure_next_singleton,
    ExponentialClock.law_tail 0 (mul_nonneg (positive s).le ht), mul_comm]

end OddCycle.FiniteMarkov
