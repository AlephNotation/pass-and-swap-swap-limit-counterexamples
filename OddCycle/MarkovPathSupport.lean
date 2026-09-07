import OddCycle.MarkovPathMeasure

/-! Almost every trajectory uses only positive-probability transitions. -/

namespace OddCycle.FiniteMarkov

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable (P : FiniteMarkov S)

theorem pathMeasureFrom_next {a : Nat} (x : Prefix S a) :
    (P.pathMeasureFrom x).map (fun y => y (a + 1)) = P.rowMeasure (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) := by
  change (Kernel.traj (X := fun _ => S) P.historyKernel a x).map _ = _
  rw [← Kernel.map_apply _ (measurable_pi_apply (X := fun _ : Nat => S) (a + 1)),
    Kernel.map_traj_succ_self]
  rfl

theorem rowMeasure_ae_positive (s : S) : ∀ᵐ t ∂P.rowMeasure s, 0 < P.prob s t := by
  rw [ae_iff_of_countable]
  intro t ht
  by_contra h
  have hz : P.prob s t = 0 := le_antisymm (le_of_not_gt h) (P.nonneg s t)
  exact ht (by rw [P.rowMeasure_singleton, hz, ENNReal.ofReal_zero])

theorem pathMeasureFrom_ae_next {a : Nat} (x : Prefix S a) :
    ∀ᵐ y ∂P.pathMeasureFrom x, 0 < P.prob (y a) (y (a + 1)) := by
  have hh : ∀ᵐ t ∂(P.pathMeasureFrom x).map (fun y => y (a + 1)),
      0 < P.prob (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) t := by
    rw [P.pathMeasureFrom_next]
    exact P.rowMeasure_ae_positive _
  have ht := (ae_map_iff (measurable_pi_apply (X := fun _ : Nat => S) (a + 1)).aemeasurable
    (Set.to_countable {t | 0 < P.prob (x ⟨a, Finset.mem_Iic.mpr le_rfl⟩) t}).measurableSet).mp hh
  filter_upwards [ht, P.pathMeasureFrom_ae_current x] with y hy he
  rwa [he]

theorem pathMeasure_ae_steps (s : S) :
    ∀ᵐ y ∂P.pathMeasure s, ∀ n, 0 < P.prob (y n) (y (n + 1)) := by
  rw [ae_all_iff]
  intro n
  have hm : MeasurableSet {y : Nat → S | 0 < P.prob (y n) (y (n + 1))} := by
    exact ((measurable_of_countable (fun p : S × S => P.prob p.1 p.2)).comp
      ((measurable_pi_apply (X := fun _ : Nat => S) n).prodMk (measurable_pi_apply (X := fun _ : Nat => S) (n + 1)))) measurableSet_Ioi
  unfold pathMeasure pathMeasureFrom
  rw [← Kernel.traj_comp_partialTraj (X := fun _ => S) (κ := P.historyKernel) (Nat.zero_le n)]
  exact Kernel.ae_comp_of_ae_ae hm (Filter.Eventually.of_forall (fun x => P.pathMeasureFrom_ae_next x))

end OddCycle.FiniteMarkov
