import OddCycle.CanonicalLengthProjection
import OddCycle.ConstantRateStationary
import OddCycle.CycleContinuousTime

/-! Queue-length indistinguishability for the existing continuous-time queue
process, with an actual stationary comparison initialization. -/

noncomputable section

namespace OddCycle

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

instance (states : List State) : MeasurableSpace (ClassState states) := ⊤
instance (states : List State) : MeasurableSingletonClass (ClassState states) := ⟨fun _ => trivial⟩

namespace ClosedClass

variable {n w : Nat} {states : List State} (hc : ClosedClass n w states)

def fullInitial (v : ClassState states → ℝ) : CycleState n → ℝ := FiniteMarkov.push hc.embedding v

/-- Law of full trajectories of the original queue process, started in this class. -/
def configurationLaw (hn : 0 < n) (v : ClassState states → ℝ) : Measure (ℝ≥0 → CycleState n) :=
  (((unitPositions n).kernel hn w).mixedTimedLaw (hc.fullInitial v)).map
    (fun ω t => (unitPositions n).process hn ω t)

def lengthPathLaw (hn : 0 < n) (v : ClassState states → ℝ) : Measure (ℝ≥0 → Nat) :=
  (hc.configurationLaw hn v).map (fun y t => (y t).val.1.length)

theorem configurationLaw_eq (hn : 0 < n) {v : ClassState states → ℝ}
    (hv : v ∈ stdSimplex ℝ (ClassState states)) :
    hc.configurationLaw hn v = ((hc.unitKernel hn).mixedTimedLaw v).map
      (fun ω t => hc.embedding (FiniteMarkov.timedState (fun _ => (n : ℝ))
        (fun _ => by exact Nat.cast_pos.mpr hn) ω t)) := by
  exact ((hc.unitKernel_embedding hn).observed_timed_pathLaw
    (fun _ => (n : ℝ)) (unitPositions n).total (fun _ => by exact Nat.cast_pos.mpr hn)
    ((unitPositions n).total_pos hn) (fun s => (unitPositions_total (hc.embedding s)).symm) hv).symm

theorem lengthPathLaw_eq (hn : 0 < n) {v : ClassState states → ℝ}
    (hv : v ∈ stdSimplex ℝ (ClassState states)) :
    hc.lengthPathLaw hn v = ((hc.unitKernel hn).mixedTimedLaw v).map
      (fun ω t => (FiniteMarkov.timedState (fun _ => (n : ℝ))
        (fun _ => by exact Nat.cast_pos.mpr hn) ω t).val.1.length) := by
  have hm : Measurable (fun (y : ℝ≥0 → CycleState n) t => (y t).val.1.length) :=
    measurable_pi_lambda _ (fun t => (measurable_of_countable (fun s : CycleState n => s.val.1.length)).comp
      (measurable_pi_apply (X := fun _ => CycleState n) t))
  have he : Measurable (fun (ω : FiniteMarkov.TimedSample (ClassState states)) t =>
      hc.embedding (FiniteMarkov.timedState (fun _ => (n : ℝ)) (fun _ => by exact Nat.cast_pos.mpr hn) ω t)) :=
    measurable_pi_lambda _ (fun t => (measurable_of_countable hc.embedding).comp
      (FiniteMarkov.timedState_measurable _ _ t))
  rw [lengthPathLaw, hc.configurationLaw_eq hn hv, Measure.map_map hm he]
  rfl

theorem canonical_queue_length_indistinguishable (hn : 0 < n) {π : ClassState states → ℝ}
    (hπ : π ∈ stdSimplex ℝ (ClassState states)) (hstat : (hc.unitKernel hn).StationaryVector π) :
    hc.lengthPathLaw hn hc.unitCanonical = hc.lengthPathLaw hn π := by
  have h := (hc.unitKernel_lumps hn).timed_indistinguishable
    (fun _ => (n : ℝ)) (fun _ => (n : ℝ)) (fun _ => by exact Nat.cast_pos.mpr hn)
    (fun _ => by exact Nat.cast_pos.mpr hn) (fun _ => rfl) hc.unitCanonical_simplex hπ
    (hc.unitCanonical_same_marginal hn hπ hstat)
  have hm : Measurable (fun (y : ℝ≥0 → Fin (n + 1)) t => (y t).val) :=
    measurable_pi_lambda _ (fun t => (measurable_of_countable Fin.val).comp
      (measurable_pi_apply (X := fun _ => Fin (n + 1)) t))
  have ho : Measurable (fun (ω : FiniteMarkov.TimedSample (ClassState states)) t =>
      hc.queueLength (FiniteMarkov.timedState (fun _ => (n : ℝ)) (fun _ => by exact Nat.cast_pos.mpr hn) ω t)) :=
    measurable_pi_lambda _ (fun t => (measurable_of_countable hc.queueLength).comp
      (FiniteMarkov.timedState_measurable _ _ t))
  have he := congrArg (fun μ : Measure (ℝ≥0 → Fin (n + 1)) => μ.map (fun y t => (y t).val)) h
  dsimp only at he
  rw [Measure.map_map hm ho, Measure.map_map hm ho] at he
  rw [hc.lengthPathLaw_eq hn hc.unitCanonical_simplex, hc.lengthPathLaw_eq hn hπ]
  exact he

theorem configurationLaw_stationary_current (hn : 0 < n) {π : ClassState states → ℝ}
    (hπ : π ∈ stdSimplex ℝ (ClassState states)) (hstat : (hc.unitKernel hn).StationaryVector π)
    (t : ℝ≥0) (j : CycleState n) :
    hc.configurationLaw hn π {y | y t = j} = ENNReal.ofReal (hc.fullInitial π j) := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil states hc.nonempty
  letI : Nonempty (CycleState n) := ⟨hc.embedding ⟨s, List.mem_toFinset.mpr hs⟩⟩
  have hm : Measurable (fun (ω : FiniteMarkov.TimedSample (CycleState n)) t => (unitPositions n).process hn ω t) :=
    measurable_pi_lambda _ (fun t => (unitPositions n).process_measurable hn t)
  have hA : MeasurableSet {y : ℝ≥0 → CycleState n | y t = j} :=
    (measurable_pi_apply (X := fun _ => CycleState n) t) (measurableSet_singleton j)
  rw [configurationLaw, Measure.map_apply hm hA]
  have he (ω : FiniteMarkov.TimedSample (CycleState n)) : (unitPositions n).process hn ω t =
      FiniteMarkov.timedState (fun _ => (n : ℝ)) (fun _ => by exact Nat.cast_pos.mpr hn) ω t := by
    exact FiniteMarkov.timedState_projection (unitPositions n).total (fun _ => (n : ℝ))
      ((unitPositions n).total_pos hn) (fun _ => by exact Nat.cast_pos.mpr hn) id (fun s => unitPositions_total s) ω t
  change ((unitPositions n).kernel hn w).mixedTimedLaw (hc.fullInitial π)
    {ω | (unitPositions n).process hn ω t = j} = _
  simp_rw [he]
  exact ((unitPositions n).kernel hn w).constantRate_stationary_current n (by exact Nat.cast_pos.mpr hn)
    (FiniteMarkov.push_simplex _ hπ) ((hc.unitKernel_embedding hn).push_stationary hstat) t j

end ClosedClass
end OddCycle
