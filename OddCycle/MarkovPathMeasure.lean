import OddCycle.FiniteAbsorption
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Countably infinite trajectories of the finite completion chain, built by
Mathlib's Ionescu--Tulcea theorem. No path-space existence axiom is added. -/

namespace OddCycle.FiniteMarkov

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable (P : FiniteMarkov S)

noncomputable def rowPMF (s : S) : PMF S :=
  PMF.ofFintype (fun t => ENNReal.ofReal (P.prob s t)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => P.nonneg s t), P.sum_one]
    simp)

noncomputable def rowMeasure (s : S) : Measure S := (P.rowPMF s).toMeasure

instance rowMeasure_probability (s : S) : IsProbabilityMeasure (P.rowMeasure s) := by
  unfold rowMeasure
  infer_instance

theorem rowMeasure_singleton (s t : S) : P.rowMeasure s {t} = ENNReal.ofReal (P.prob s t) := by
  exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton t)

theorem rowMeasure_lintegral (s : S) (f : S → ℝ≥0∞) :
    ∫⁻ t, f t ∂P.rowMeasure s = ∑ t, ENNReal.ofReal (P.prob s t) * f t := by
  rw [lintegral_fintype]
  simp only [P.rowMeasure_singleton, mul_comm]

abbrev Prefix (S : Type*) (a : Nat) := (i : Finset.Iic a) → S

def extendPrefix {a : Nat} (x : Prefix S a) (s : S) : Prefix S (a + 1) :=
  IicProdIoc (X := fun _ => S) a (a + 1) (x, MeasurableEquiv.piSingleton (X := fun _ => S) a s)

omit [Fintype S] [MeasurableSingletonClass S] in
@[simp] theorem extendPrefix_last {a : Nat} (x : Prefix S a) (s : S) :
    extendPrefix x s ⟨a + 1, Finset.mem_Iic.mpr le_rfl⟩ = s := by
  simp [extendPrefix, IicProdIoc, MeasurableEquiv.piSingleton]

noncomputable def historyKernel (a : Nat) : Kernel (Prefix S a) S where
  toFun x := P.rowMeasure (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := measurable_of_countable _

instance historyKernel_markov (a : Nat) : IsMarkovKernel (P.historyKernel a) :=
  ⟨fun _ => P.rowMeasure_probability _⟩

noncomputable def pathMeasureFrom {a : Nat} (x : Prefix S a) : Measure (Nat → S) :=
  Kernel.traj P.historyKernel a x

instance pathMeasureFrom_probability {a : Nat} (x : Prefix S a) : IsProbabilityMeasure (P.pathMeasureFrom x) := by
  unfold pathMeasureFrom
  infer_instance

noncomputable def pathMeasure (s : S) : Measure (Nat → S) := P.pathMeasureFrom (a := 0) (fun _ => s)

instance pathMeasure_probability (s : S) : IsProbabilityMeasure (P.pathMeasure s) :=
  P.pathMeasureFrom_probability _

theorem partialTraj_next_lintegral {a : Nat} (x : Prefix S a) (f : Prefix S (a + 1) → ℝ≥0∞) :
    ∫⁻ y, f y ∂Kernel.partialTraj (X := fun _ => S) P.historyKernel a (a + 1) x =
      ∑ s, ENNReal.ofReal (P.prob (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) s) * f (extendPrefix x s) := by
  rw [Kernel.partialTraj_succ_self]
  rw [Kernel.lintegral_map _ (measurable_IicProdIoc (X := fun _ => S) (m := a) (n := a + 1)) _ (measurable_of_countable f)]
  rw [Kernel.lintegral_id_prod (measurable_of_countable _) _]
  rw [Kernel.lintegral_map _ (MeasurableEquiv.piSingleton (X := fun _ => S) a).measurable _ (measurable_of_countable _)]
  exact P.rowMeasure_lintegral _ _

theorem pathMeasureFrom_step {a : Nat} (x : Prefix S a) {A : Set (Nat → S)} (hA : MeasurableSet A) :
    P.pathMeasureFrom x A =
      ∑ s, ENNReal.ofReal (P.prob (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) s) * P.pathMeasureFrom (extendPrefix x s) A := by
  rw [pathMeasureFrom, ← Kernel.traj_comp_partialTraj (X := fun _ => S) (κ := P.historyKernel) (Nat.le_succ a)]
  rw [Kernel.comp_apply' _ _ _ hA]
  exact P.partialTraj_next_lintegral x _

theorem pathMeasureFrom_current {a : Nat} (x : Prefix S a) :
    (P.pathMeasureFrom x).map (fun y => y a) = Measure.dirac (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) := by
  have he : (fun y : Nat → S => y a) = (fun z : Prefix S a => z ⟨a, Finset.mem_Iic.mpr le_rfl⟩) ∘ frestrictLe a := rfl
  rw [he, ← Measure.map_map (measurable_of_countable (fun z : Prefix S a => z ⟨a, Finset.mem_Iic.mpr le_rfl⟩)) (measurable_frestrictLe (X := fun _ => S) a), pathMeasureFrom,
    Kernel.traj_map_frestrictLe_apply (X := fun _ => S), Kernel.partialTraj_self, Kernel.id_apply, Measure.map_dirac (measurable_of_countable _)]

theorem pathMeasureFrom_ae_current {a : Nat} (x : Prefix S a) :
    ∀ᵐ y ∂P.pathMeasureFrom x, y a = x ⟨a, Finset.mem_Iic.mpr le_rfl⟩ := by
  have he := P.pathMeasureFrom_current x
  have hh : ∀ᵐ z ∂(P.pathMeasureFrom x).map (fun y => y a), z = x ⟨a, Finset.mem_Iic.mpr le_rfl⟩ := by
    rw [he]
    simp
  exact (ae_map_iff (measurable_pi_apply a).aemeasurable (by measurability)).mp hh

end OddCycle.FiniteMarkov
