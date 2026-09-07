import OddCycle.MarkovPathMeasure

/-! The previously defined finite-horizon probabilities are probabilities
of measurable events on the constructed infinite trajectory space. -/

namespace OddCycle.FiniteMarkov

open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped ENNReal Topology

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable (P : FiniteMarkov S) (A : S → Prop) [DecidablePred A]

def futureAvoid (a m : Nat) : Set (Nat → S) := {y | ∀ j, j ≤ m → ¬ A (y (a + j))}

omit [DecidablePred A] in
theorem futureAvoid_measurable (a m : Nat) : MeasurableSet (futureAvoid A a m) := by
  have hA : MeasurableSet {s | A s} := (Set.to_countable _).measurableSet
  simp only [futureAvoid, setOf_forall]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
    ((measurable_pi_apply (a + j)) hA).compl))

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [DecidablePred A] in
theorem futureAvoid_succ (a m : Nat) (y : Nat → S) :
    y ∈ futureAvoid A a (m + 1) ↔ ¬ A (y a) ∧ y ∈ futureAvoid A (a + 1) m := by
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by omega), fun j hj => by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using h (j + 1) (by omega)⟩
  · rintro ⟨ha, h⟩ j hj
    cases j with
    | zero => simpa using ha
    | succ j => simpa only [Nat.add_assoc, Nat.add_comm 1 j] using h j (by omega)

theorem pathMeasureFrom_avoid {a : Nat} (x : Prefix S a) (m : Nat) :
    P.pathMeasureFrom x (futureAvoid A a m) =
      ENNReal.ofReal (P.avoidSet A m (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩)) := by
  induction m generalizing a with
  | zero =>
    have he : futureAvoid A a 0 =ᵐ[P.pathMeasureFrom x]
        (if A (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) then (∅ : Set (Nat → S)) else Set.univ) := by
      filter_upwards [P.pathMeasureFrom_ae_current x] with y hy
      apply propext
      change (y ∈ futureAvoid A a 0) ↔ y ∈ (if A (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) then (∅ : Set (Nat → S)) else Set.univ)
      simp only [futureAvoid, Set.mem_setOf_eq, Nat.le_zero_eq, forall_eq, Nat.add_zero, hy]
      split_ifs <;> simp_all
    rw [measure_congr he]
    simp only [avoidSet]
    split_ifs <;> simp
  | succ m ih =>
    have he : futureAvoid A a (m + 1) =ᵐ[P.pathMeasureFrom x]
        (if A (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) then (∅ : Set (Nat → S)) else futureAvoid A (a + 1) m) := by
      filter_upwards [P.pathMeasureFrom_ae_current x] with y hy
      apply propext
      change (y ∈ futureAvoid A a (m + 1)) ↔ y ∈ (if A (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) then (∅ : Set (Nat → S)) else futureAvoid A (a + 1) m)
      rw [futureAvoid_succ, hy]
      split_ifs <;> simp_all only [Set.mem_empty_iff_false, false_and, not_true_eq_false, not_false_eq_true, true_and]
    rw [measure_congr he, avoidSet]
    split_ifs with hx
    · simp
    · rw [P.pathMeasureFrom_step x (futureAvoid_measurable A (a + 1) m)]
      simp only [ih, extendPrefix_last, expect]
      rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => mul_nonneg (P.nonneg _ s) (P.avoidSet_nonneg A m s))]
      apply Finset.sum_congr rfl
      intro s _
      rw [ENNReal.ofReal_mul (P.nonneg _ s)]

theorem pathMeasure_avoid (s : S) (m : Nat) :
    P.pathMeasure s (futureAvoid A 0 m) = ENNReal.ofReal (P.avoidSet A m s) :=
  P.pathMeasureFrom_avoid A (fun _ => s) m

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [DecidablePred A] in
theorem futureAvoid_antitone (a : Nat) : Antitone (futureAvoid A a) := by
  intro m k hmk y hy j hj
  exact hy j (hj.trans hmk)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [DecidablePred A] in
theorem futureAvoid_inter (a : Nat) : (⋂ m, futureAvoid A a m) = {y | ∀ j, ¬ A (y (a + j))} := by
  ext y
  simp only [Set.mem_iInter, futureAvoid, Set.mem_setOf_eq]
  exact ⟨fun h j => h j j le_rfl, fun h _ j _ => h j⟩

theorem pathMeasure_ever_hit (s : S)
    (h : Tendsto (fun m => P.avoidSet A m s) atTop (𝓝 0)) :
    P.pathMeasure s {y | ∃ j, A (y j)} = 1 := by
  have hlim := tendsto_measure_iInter_atTop (fun m => (futureAvoid_measurable A 0 m).nullMeasurableSet)
    (futureAvoid_antitone A 0) (⟨0, measure_ne_top _ _⟩ : ∃ m, P.pathMeasure s (futureAvoid A 0 m) ≠ ∞)
  simp only [Function.comp_def, P.pathMeasure_avoid A, futureAvoid_inter A, Nat.zero_add] at hlim
  have hz : P.pathMeasure s {y | ∀ j, ¬ A (y j)} = 0 :=
    tendsto_nhds_unique hlim (by simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp h)
  have hcomp : {y : Nat → S | ∃ j, A (y j)} = {y | ∀ j, ¬ A (y j)}ᶜ := by ext y; simp
  have hm : MeasurableSet {y : Nat → S | ∀ j, ¬ A (y j)} := by
    simpa only [futureAvoid_inter, Nat.zero_add] using MeasurableSet.iInter (futureAvoid_measurable A 0)
  rw [hcomp, measure_compl hm (measure_ne_top _ _), hz, measure_univ, tsub_zero]

end OddCycle.FiniteMarkov
