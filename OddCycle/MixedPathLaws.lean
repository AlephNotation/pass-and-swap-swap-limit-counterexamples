import OddCycle.PathLumping
import OddCycle.TimedStateMeasurable

/-! Initial probability mixtures and exact observation laws, including the
existing independent-exponential-clock construction. -/

noncomputable section

namespace OddCycle.FiniteMarkov

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable [MeasurableSpace T] [MeasurableSingletonClass T]

def mixedPathLaw (P : FiniteMarkov S) (v : S → ℝ) : Measure (Nat → S) :=
  ∑ s, ENNReal.ofReal (v s) • P.pathMeasure s

theorem mixedPathLaw_apply (P : FiniteMarkov S) (v : S → ℝ) (A : Set (Nat → S)) :
    P.mixedPathLaw v A = ∑ s, ENNReal.ofReal (v s) * P.pathMeasure s A := by
  simp only [mixedPathLaw, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]

theorem mixedPathLaw_probability (P : FiniteMarkov S) {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) :
    IsProbabilityMeasure (P.mixedPathLaw v) := by
  constructor
  rw [P.mixedPathLaw_apply]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hv.1 s), hv.2, ENNReal.ofReal_one]

omit [Fintype T] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T] [MeasurableSingletonClass T] in
theorem push_ofReal (f : S → T) {v : S → ℝ} (hv : ∀ s, 0 ≤ v s) (j : T) :
    ENNReal.ofReal (push f v j) = ∑ s, if f s = j then ENNReal.ofReal (v s) else 0 := by
  unfold push
  rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => by split_ifs; exact hv s; exact le_rfl)]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

variable {P : FiniteMarkov S} {R : FiniteMarkov T} {f : S → T}

theorem LumpsTo.mixedPathLaw_map (h : P.LumpsTo R f) {v : S → ℝ} (hv : ∀ s, 0 ≤ v s) :
    (P.mixedPathLaw v).map (fun y i => f (y i)) = R.mixedPathLaw (push f v) := by
  have hm : Measurable (fun (y : Nat → S) i => f (y i)) :=
    measurable_pi_lambda _ (fun i => (measurable_of_countable f).comp (measurable_pi_apply (X := fun _ => S) i))
  ext A hA
  rw [Measure.map_apply hm hA, mixedPathLaw_apply, mixedPathLaw_apply]
  have he (s : S) : P.pathMeasure s ((fun y i => f (y i)) ⁻¹' A) = R.pathMeasure (f s) A := by
    rw [← Measure.map_apply hm hA, h.pathMeasure_map]
  simp_rw [he, push_ofReal f hv]
  exact sum_fibers f (fun s => ENNReal.ofReal (v s)) (fun j => R.pathMeasure j A)

def mixedTimedLaw (P : FiniteMarkov S) (v : S → ℝ) : Measure (TimedSample S) :=
  (P.mixedPathLaw v).prod ExponentialClock.law

theorem mixedTimedLaw_probability (P : FiniteMarkov S) {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) :
    IsProbabilityMeasure (P.mixedTimedLaw v) := by
  letI := P.mixedPathLaw_probability hv
  unfold mixedTimedLaw
  infer_instance

theorem LumpsTo.mixedTimedLaw_map (h : P.LumpsTo R f) {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) :
    (P.mixedTimedLaw v).map (Prod.map (fun y i => f (y i)) id) = R.mixedTimedLaw (push f v) := by
  letI := P.mixedPathLaw_probability hv
  have hm : Measurable (fun (y : Nat → S) i => f (y i)) :=
    measurable_pi_lambda _ (fun i => (measurable_of_countable f).comp (measurable_pi_apply (X := fun _ => S) i))
  unfold mixedTimedLaw
  rw [← Measure.map_prod_map _ _ hm measurable_id, h.mixedPathLaw_map hv.1, Measure.map_id]

omit [DecidableEq T] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T] [MeasurableSingletonClass T] in
theorem timedState_projection (rateS : S → ℝ) (rateT : T → ℝ)
    (hS : ∀ s, 0 < rateS s) (hT : ∀ t, 0 < rateT t) (f : S → T)
    (hr : ∀ s, rateS s = rateT (f s)) (ω : TimedSample S) (t : ℝ≥0) :
    f (timedState rateS hS ω t) = timedState rateT hT (Prod.map (fun y i => f (y i)) id ω) t := by
  have ha (m : Nat) : ClockedPath.arrival rateS ω.1 ω.2 m =
      ClockedPath.arrival rateT (fun i => f (ω.1 i)) ω.2 m := by
    simp only [ClockedPath.arrival, hr]
  have hi : ClockedPath.index rateS hS ω.1 ω.2 t =
      ClockedPath.index rateT hT (fun i => f (ω.1 i)) ω.2 t := by
    apply Eq.symm
    apply (ClockedPath.index_eq_iff rateT hT _ _ t _).mpr
    rw [← ha, ← ha]
    exact ⟨ClockedPath.index_lower rateS hS _ _ t, ClockedPath.index_upper rateS hS _ _ t⟩
  change f (ω.1 (ClockedPath.index rateS hS ω.1 ω.2 t)) =
    f (ω.1 (ClockedPath.index rateT hT (fun i => f (ω.1 i)) ω.2 t))
  rw [hi]

theorem LumpsTo.observed_timed_pathLaw (h : P.LumpsTo R f)
    (rateS : S → ℝ) (rateT : T → ℝ) (hS : ∀ s, 0 < rateS s) (hT : ∀ t, 0 < rateT t)
    (hr : ∀ s, rateS s = rateT (f s)) {v : S → ℝ} (hv : v ∈ stdSimplex ℝ S) :
    (P.mixedTimedLaw v).map (fun ω t => f (timedState rateS hS ω t)) =
      (R.mixedTimedLaw (push f v)).map (fun ω t => timedState rateT hT ω t) := by
  have hm : Measurable (Prod.map (fun (y : Nat → S) i => f (y i)) (id : ExponentialClock.Clock → ExponentialClock.Clock)) := by
    apply Measurable.prodMap _ measurable_id
    exact measurable_pi_lambda _ (fun i => (measurable_of_countable f).comp (measurable_pi_apply (X := fun _ => S) i))
  have ht : Measurable (fun (ω : TimedSample T) t => timedState rateT hT ω t) :=
    measurable_pi_lambda _ (fun t => timedState_measurable rateT hT t)
  rw [← h.mixedTimedLaw_map hv, Measure.map_map ht hm]
  congr 1
  funext ω t
  exact timedState_projection rateS rateT hS hT f hr ω t

theorem LumpsTo.timed_indistinguishable (h : P.LumpsTo R f)
    (rateS : S → ℝ) (rateT : T → ℝ) (hS : ∀ s, 0 < rateS s) (hT : ∀ t, 0 < rateT t)
    (hr : ∀ s, rateS s = rateT (f s)) {v u : S → ℝ}
    (hv : v ∈ stdSimplex ℝ S) (hu : u ∈ stdSimplex ℝ S) (he : push f v = push f u) :
    (P.mixedTimedLaw v).map (fun ω t => f (timedState rateS hS ω t)) =
      (P.mixedTimedLaw u).map (fun ω t => f (timedState rateS hS ω t)) := by
  rw [h.observed_timed_pathLaw rateS rateT hS hT hr hv,
    h.observed_timed_pathLaw rateS rateT hS hT hr hu, he]

end OddCycle.FiniteMarkov
