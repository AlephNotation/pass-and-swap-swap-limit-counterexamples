import OddCycle.ContinuousTimePaths

/-! The clocked process is a measurable random variable at every real time,
and is constant between successive completion epochs. -/

namespace OddCycle.FiniteMarkov

open MeasureTheory Set
open scoped NNReal

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable (rate : S → ℝ) (positive : ∀ s, 0 < rate s)

theorem eventTime_measurable (n : Nat) : Measurable (fun ω : TimedSample S => eventTime rate ω n) := by
  unfold eventTime ClockedPath.arrival
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_snd)).div
    ((measurable_of_countable rate).comp ((measurable_pi_apply i).comp measurable_fst))

theorem timedIndex_measurable (t : ℝ≥0) :
    Measurable (fun ω : TimedSample S => ClockedPath.index rate positive ω.1 ω.2 t) := by
  apply measurable_to_countable'
  intro n
  have he : (fun ω : TimedSample S => ClockedPath.index rate positive ω.1 ω.2 t) ⁻¹' {n} =
      {ω | eventTime rate ω n ≤ t} ∩ {ω | t < eventTime rate ω (n + 1)} := by
    ext ω
    exact ClockedPath.index_eq_iff rate positive ω.1 ω.2 t n
  rw [he]
  exact (measurableSet_le (eventTime_measurable rate n) measurable_const).inter
    (measurableSet_lt measurable_const (eventTime_measurable rate (n + 1)))

theorem timedState_measurable (t : ℝ≥0) : Measurable (fun ω : TimedSample S => timedState rate positive ω t) := by
  intro B hB
  have he : (fun ω : TimedSample S => timedState rate positive ω t) ⁻¹' B =
      ⋃ n : Nat, {ω | ClockedPath.index rate positive ω.1 ω.2 t = n} ∩ {ω | ω.1 n ∈ B} := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro h
      exact ⟨_, rfl, h⟩
    · rintro ⟨n, hn, h⟩
      simpa only [timedState, ClockedPath.state, hn] using h
  rw [he]
  apply MeasurableSet.iUnion
  intro n
  exact ((timedIndex_measurable rate positive t) (measurableSet_singleton n)).inter
    (((measurable_pi_apply n).comp measurable_fst) hB)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem timedState_between (ω : TimedSample S) (t : ℝ≥0) (n : Nat)
    (hl : eventTime rate ω n ≤ t) (hu : t < eventTime rate ω (n + 1)) :
    timedState rate positive ω t = ω.1 n := ClockedPath.state_between rate positive ω.1 ω.2 t n hl hu

end OddCycle.FiniteMarkov
