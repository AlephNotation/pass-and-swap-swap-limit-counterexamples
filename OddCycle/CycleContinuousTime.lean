import OddCycle.ContinuousAbsorption
import OddCycle.CompletionKernel

/-! Measure-one recurrence and absorption for the original queue process with
arbitrary strictly positive time-homogeneous position completion rates. -/

namespace OddCycle

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

instance (n : Nat) : MeasurableSpace (CycleState n) := ⊤
instance (n : Nat) : MeasurableSingletonClass (CycleState n) := ⟨fun _ => trivial⟩

namespace PositivePositionAllocation

variable {n : Nat} (a : PositivePositionAllocation n)

noncomputable def pathLaw (hn : 0 < n) (w : Nat) (s : CycleState n) := (a.kernel hn w).timedLaw s

noncomputable def process (hn : 0 < n) (ω : FiniteMarkov.TimedSample (CycleState n)) (t : ℝ≥0) :=
  FiniteMarkov.timedState a.total (a.total_pos hn) ω t

theorem process_measurable (hn : 0 < n) (t : ℝ≥0) : Measurable (fun ω => a.process hn ω t) :=
  FiniteMarkov.timedState_measurable a.total (a.total_pos hn) t

theorem process_nonexplosive (hn : 0 < n) (ω : FiniteMarkov.TimedSample (CycleState n)) :
    Tendsto (FiniteMarkov.eventTime a.total ω) atTop atTop :=
  FiniteMarkov.eventTime_nonexplosive a.total (a.total_pos hn) ω

theorem completion_rate_identity (hn : 0 < n) (w : Nat) (s t : CycleState n) :
    a.total s * (a.kernel hn w).prob s t = a.incoming w s t := by
  change a.total s * (a.incoming w s t / a.total s) = _
  field_simp [(a.total_pos hn s).ne']

theorem completion_law (hn : 0 < n) (w : Nat) (s u : CycleState n) {t : ℝ} (ht : 0 ≤ t) :
    a.pathLaw hn w s {ω | t < FiniteMarkov.eventTime a.total ω 1 ∧ ω.1 1 = u} =
      ENNReal.ofReal (Real.exp (-(a.total s * t))) * ENNReal.ofReal (a.incoming w s u / a.total s) :=
  (a.kernel hn w).first_completion_law a.total (a.total_pos hn) s u ht

theorem continuous_recurrent_iff_runs (hn : 3 ≤ n) {w : Nat} (hw : 1 ≤ w) (s : CycleState n) :
    a.pathLaw (by omega) w s (FiniteMarkov.continuousReturn a.total (a.total_pos (by omega)) s) = 1 ↔
      ShortRuns n w s.val ∨ ExceptionalRuns n w s.val := by
  rw [pathLaw, FiniteMarkov.continuous_recurrence_iff]
  exact a.recurrent_iff_runs hn hw s

attribute [local instance] Classical.propDecidable

theorem continuous_classified_absorption (hn : 3 ≤ n) {w : Nat} (hw : 1 ≤ w) (s : CycleState n) :
    a.pathLaw (by omega) w s (FiniteMarkov.continuousHit a.total (a.total_pos (by omega))
      (fun t => ShortRuns n w t.val ∨ ExceptionalRuns n w t.val)) = 1 :=
  (a.kernel (by omega) w).continuous_absorption a.total (a.total_pos (by omega)) s _
    (a.classified_absorption hn hw s)

theorem continuous_short_absorption (hn : 3 ≤ n) {w : Nat} (hw : 1 ≤ w)
    (hlength : ¬ ∃ k, 1 ≤ k ∧ n = 2 * k * w + 1) (s : CycleState n) :
    a.pathLaw (by omega) w s (FiniteMarkov.continuousHit a.total (a.total_pos (by omega))
      (fun t => ShortRuns n w t.val)) = 1 :=
  (a.kernel (by omega) w).continuous_absorption a.total (a.total_pos (by omega)) s _
    (a.short_absorption hn hw hlength s)

theorem continuous_eventually_classified (hn : 3 ≤ n) {w : Nat} (hw : 1 ≤ w) (s : CycleState n) :
    ∀ᵐ ω ∂a.pathLaw (by omega) w s, ∃ t : ℝ≥0, ∀ u : ℝ≥0, t ≤ u →
      ShortRuns n w (a.process (by omega) ω u).val ∨ ExceptionalRuns n w (a.process (by omega) ω u).val := by
  apply (a.kernel (by omega) w).continuous_eventual a.total (a.total_pos (by omega)) s _
    (a.classified_absorption hn hw s)
  intro i j hi hp
  have hterm := (CycleState.terminal_iff_runs hn hw i).mpr hi
  have hij : Relation.ReflTransGen (CycleState.Step n w) i j := .single ((a.kernel_pos_iff _ w i j).mp hp)
  apply (CycleState.terminal_iff_runs hn hw j).mp
  intro z hjz
  exact (hterm z (hij.trans hjz)).trans hij

theorem continuous_eventually_one_class (hn : 3 ≤ n) {w : Nat} (hw : 1 ≤ w) (s : CycleState n) :
    ∀ᵐ ω ∂a.pathLaw (by omega) w s, ∃ i : CycleState n, ∃ t : ℝ≥0,
      (ShortRuns n w i.val ∨ ExceptionalRuns n w i.val) ∧
      ∀ u : ℝ≥0, t ≤ u → EventReachable (cycleAdjacent n) w i.val (a.process (by omega) ω u).val ∧
        EventReachable (cycleAdjacent n) w (a.process (by omega) ω u).val i.val := by
  let P := a.kernel (by omega : 0 < n) w
  have hsupp : ∀ i j, 0 < P.prob i j → CycleState.Step n w i j ∨ i = j :=
    fun i j h => Or.inl ((a.kernel_pos_iff _ w i j).mp h)
  have hpos : ∀ i j, CycleState.Step n w i j → 0 < P.prob i j :=
    fun i j h => (a.kernel_pos_iff _ w i j).mpr h
  filter_upwards [P.continuous_eventually_one_class a.total (a.total_pos (by omega)) s] with ω hω
  obtain ⟨i, t, hi, hstay⟩ := hω
  refine ⟨i, t, (CycleState.terminal_iff_runs hn hw i).mp
    ((CycleState.kernel_terminal_iff P hsupp hpos i).mp hi), ?_⟩
  intro u hu
  exact ⟨CycleState.event_reachable_iff.mp ((CycleState.kernel_reachable_iff P hsupp hpos _ _).mp (hstay u hu).1),
    CycleState.event_reachable_iff.mp ((CycleState.kernel_reachable_iff P hsupp hpos _ _).mp (hstay u hu).2)⟩

end PositivePositionAllocation
end OddCycle
