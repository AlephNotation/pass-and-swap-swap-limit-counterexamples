import OddCycle.MixedPathLaws

/-! Completion-time marginals of the constructed infinite path law. -/

noncomputable section

namespace OddCycle.FiniteMarkov

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S : Type*} [Fintype S] [DecidableEq S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable (P : FiniteMarkov S)

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem advance_pointMass (s j : S) : P.advance (pointMass s) j = P.prob s j := by
  simp [advance, pointMass]

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem evolve_advance (v : S → ℝ) (m : Nat) : P.evolve m (P.advance v) = P.evolve (m + 1) v := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [evolve, ih]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem evolve_succ_pointMass (s : S) (m : Nat) (j : S) :
    P.evolve (m + 1) (pointMass s) j = ∑ t, P.prob s t * P.evolve m (pointMass t) j := by
  rw [← P.evolve_advance, P.evolve_mixture]
  simp only [P.advance_pointMass]

theorem pathMeasureFrom_after {a : Nat} (x : Prefix S a) (m : Nat) (j : S) :
    P.pathMeasureFrom x {y | y (a + m) = j} =
      ENNReal.ofReal (P.evolve m (pointMass (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩)) j) := by
  induction m generalizing a with
  | zero =>
    have hh := Measure.map_apply (measurable_pi_apply (X := fun _ : Nat => S) a)
      (measurableSet_singleton j) (μ := P.pathMeasureFrom x)
    rw [P.pathMeasureFrom_current] at hh
    have hp : Measure.dirac (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) {j} =
        ENNReal.ofReal (P.evolve 0 (pointMass (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩)) j) := by
      by_cases hx : x ⟨a, Finset.mem_Iic.mpr le_rfl⟩ = j
      · simp [evolve, pointMass, hx]
      · simp [evolve, pointMass, hx, Ne.symm hx]
    exact hh.symm.trans hp
  | succ m ih =>
    have hm : MeasurableSet {y : Nat → S | y (a + (m + 1)) = j} :=
      (measurable_pi_apply (X := fun _ => S) _) (measurableSet_singleton j)
    rw [P.pathMeasureFrom_step x hm]
    have he (s : S) : P.pathMeasureFrom (extendPrefix x s) {y | y (a + (m + 1)) = j} =
        ENNReal.ofReal (P.evolve m (pointMass s) j) := by
      simpa only [extendPrefix_last, show a + (m + 1) = (a + 1) + m by omega] using ih (extendPrefix x s)
    simp_rw [he]
    rw [P.evolve_succ_pointMass]
    rw [ENNReal.ofReal_sum_of_nonneg (fun s _ =>
      mul_nonneg (P.nonneg _ _) ((P.evolve_simplex (pointMass_simplex s) m).1 j))]
    apply Finset.sum_congr rfl
    intro s _
    exact (ENNReal.ofReal_mul (P.nonneg _ _)).symm

theorem mixedPathLaw_current {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) (m : Nat) (j : S) :
    P.mixedPathLaw v {y | y m = j} = ENNReal.ofReal (P.evolve m v j) := by
  rw [P.mixedPathLaw_apply, P.evolve_mixture]
  have he (s : S) : P.pathMeasure s {y | y m = j} = ENNReal.ofReal (P.evolve m (pointMass s) j) := by
    simpa only [Nat.zero_add] using P.pathMeasureFrom_after (a := 0) (fun _ => s) m j
  simp_rw [he]
  rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => mul_nonneg (hv.1 s) ((P.evolve_simplex (pointMass_simplex s) m).1 j))]
  apply Finset.sum_congr rfl
  intro s _
  exact (ENNReal.ofReal_mul (hv.1 s)).symm

theorem mixedPathLaw_stationary_current {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S)
    (hstat : P.StationaryVector π) (m : Nat) (j : S) :
    P.mixedPathLaw π {y | y m = j} = ENNReal.ofReal (π j) := by
  rw [P.mixedPathLaw_current hπ, P.evolve_stationary hstat]

end OddCycle.FiniteMarkov
