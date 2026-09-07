import OddCycle.FiniteLumping
import OddCycle.MarkovPathMeasure

/-! A proved observation projection commutes with the law of the entire
infinite completion trajectory, via finite prefixes and projective uniqueness. -/

noncomputable section

namespace OddCycle.FiniteMarkov

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
variable [MeasurableSpace S] [MeasurableSingletonClass S]
variable [MeasurableSpace T] [MeasurableSingletonClass T]
variable {P : FiniteMarkov S} {R : FiniteMarkov T} {f : S → T}

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace T] [MeasurableSingletonClass T] in
theorem LumpsTo.ennreal_expect (h : P.LumpsTo R f) (g : T → ℝ≥0∞) (s : S) :
    (∑ t, ENNReal.ofReal (P.prob s t) * g (f t)) =
      ∑ j, ENNReal.ofReal (R.prob (f s) j) * g j := by
  rw [sum_fibers f (fun t => ENNReal.ofReal (P.prob s t)) g]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [← h s j]
  unfold push
  rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => by
    split_ifs; exact P.nonneg s t; exact le_rfl)]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

def observePrefix (f : S → T) {a : Nat} (x : Prefix S a) : Prefix T a := fun i => f (x i)

omit [Fintype S] [Fintype T] [DecidableEq T] [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
theorem observePrefix_extend (f : S → T) {a : Nat} (x : Prefix S a) (s : S) :
    observePrefix f (extendPrefix x s) = extendPrefix (observePrefix f x) (f s) := by
  funext i
  simp only [observePrefix, extendPrefix, IicProdIoc]
  split_ifs
  · rfl
  · simp [MeasurableEquiv.piSingleton]

theorem pathMeasureFrom_prefix_le (P : FiniteMarkov S) {a b : Nat} (h : b ≤ a) (x : Prefix S a) :
    (P.pathMeasureFrom x).map (frestrictLe b) = Measure.dirac (frestrictLe₂ (π := fun _ => S) h x) := by
  rw [pathMeasureFrom, Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_le h,
    Kernel.deterministic_apply]

theorem LumpsTo.observed_prefix (h : P.LumpsTo R f) {a b : Nat} (x : Prefix S a) :
    (P.pathMeasureFrom x).map (fun y => observePrefix f (frestrictLe b y)) =
      (R.pathMeasureFrom (observePrefix f x)).map (frestrictLe b) := by
  have base {a b : Nat} (hab : b ≤ a) (x : Prefix S a) :
      (P.pathMeasureFrom x).map (fun y => observePrefix f (frestrictLe b y)) =
        (R.pathMeasureFrom (observePrefix f x)).map (frestrictLe b) := by
    change (P.pathMeasureFrom x).map (observePrefix f (a := b) ∘ frestrictLe b) = _
    rw [← Measure.map_map (measurable_of_countable (observePrefix f (a := b)))
      (measurable_frestrictLe (X := fun _ => S) b),
      pathMeasureFrom_prefix_le P hab, pathMeasureFrom_prefix_le R hab,
      Measure.map_dirac (measurable_of_countable _)]
    rfl
  have aux (d : Nat) : ∀ a b, b ≤ a + d → ∀ x : Prefix S a,
      (P.pathMeasureFrom x).map (fun y => observePrefix f (frestrictLe b y)) =
        (R.pathMeasureFrom (observePrefix f x)).map (frestrictLe b) := by
    induction d with
    | zero => intro a b hab x; exact base (by omega) x
    | succ d ih =>
      intro a b hab x
      by_cases hba : b ≤ a
      · exact base hba x
      · have hm : Measurable (fun y : Nat → S => observePrefix f (frestrictLe b y)) :=
          (measurable_of_countable (observePrefix f)).comp (measurable_frestrictLe b)
        ext A hA
        rw [Measure.map_apply hm hA, Measure.map_apply (measurable_frestrictLe b) hA,
          P.pathMeasureFrom_step (x := x) (hm hA),
          R.pathMeasureFrom_step (x := observePrefix f x) ((measurable_frestrictLe b) hA)]
        have he (s : S) : P.pathMeasureFrom (extendPrefix x s)
            ((fun y => observePrefix f (frestrictLe b y)) ⁻¹' A) =
            R.pathMeasureFrom (extendPrefix (observePrefix f x) (f s)) ((frestrictLe b) ⁻¹' A) := by
          rw [← Measure.map_apply hm hA, ih (a + 1) b (by omega), observePrefix_extend,
            Measure.map_apply (measurable_frestrictLe b) hA]
        simp_rw [he]
        exact h.ennreal_expect
          (fun j => R.pathMeasureFrom (extendPrefix (observePrefix f x) j) ((frestrictLe b) ⁻¹' A))
          (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩)
  exact aux b a b (by omega) x

theorem LumpsTo.pathMeasureFrom_map (h : P.LumpsTo R f) {a : Nat} (x : Prefix S a) :
    (P.pathMeasureFrom x).map (fun y i => f (y i)) = R.pathMeasureFrom (observePrefix f x) := by
  have hr := Kernel.isProjectiveLimit_trajFun (X := fun _ => T) R.historyKernel a (observePrefix f x)
  change IsProjectiveLimit (R.pathMeasureFrom (observePrefix f x)) _ at hr
  letI (i : Finset Nat) : IsFiniteMeasure
      (inducedFamily (X := fun _ => T)
        (fun b => Kernel.partialTraj (X := fun _ => T) R.historyKernel a b (observePrefix f x)) i) := by
    rw [← hr i]
    infer_instance
  apply Eq.symm
  apply hr.unique
  rw [isProjectiveLimit_nat_iff (Kernel.isProjectiveMeasureFamily_partialTraj (X := fun _ => T) R.historyKernel _)]
  intro b
  have hm : Measurable (fun (y : Nat → S) i => f (y i)) :=
    measurable_pi_lambda _ (fun i => (measurable_of_countable f).comp (measurable_pi_apply (X := fun _ => S) i))
  rw [inducedFamily_Iic, Measure.map_map (measurable_frestrictLe (X := fun _ => T) b) hm]
  change (P.pathMeasureFrom x).map (fun y => observePrefix f (frestrictLe b y)) = _
  rw [h.observed_prefix, pathMeasureFrom, Kernel.traj_map_frestrictLe_apply]

theorem LumpsTo.pathMeasure_map (h : P.LumpsTo R f) (s : S) :
    (P.pathMeasure s).map (fun y i => f (y i)) = R.pathMeasure (f s) :=
  h.pathMeasureFrom_map (fun _ => s)

end OddCycle.FiniteMarkov
