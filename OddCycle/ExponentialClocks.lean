import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! An explicit probability space of independent unit exponential clocks.
Almost every clock is strictly positive and has unbounded accumulated time. -/

namespace OddCycle.ExponentialClock

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

local instance : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)

noncomputable def rawLaw : Measure (Nat → ℝ) := Measure.infinitePi (fun _ => expMeasure 1)

instance : IsProbabilityMeasure rawLaw := by unfold rawLaw; infer_instance

theorem rawLaw_eval (i : Nat) : rawLaw.map (fun z => z i) = expMeasure 1 :=
  Measure.infinitePi_map_eval _ i

theorem exponential_tail {t : ℝ} (ht : 0 ≤ t) :
    expMeasure 1 (Ioi t) = ENNReal.ofReal (Real.exp (-t)) := by
  have hc : (expMeasure 1).real (Iic t) = 1 - Real.exp (-t) := by
    simpa only [cdf_eq_real, if_pos ht, one_mul] using cdf_expMeasure_eq (r := 1) (by norm_num) t
  have he : expMeasure 1 (Iic t) = ENNReal.ofReal (1 - Real.exp (-t)) := by
    rw [← hc, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hle : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [show Ioi t = (Iic t)ᶜ by ext x; simp, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ, he]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr hle)]
  congr 1
  ring

theorem rawLaw_positive : ∀ᵐ z ∂rawLaw, ∀ i, 0 < z i := by
  apply ae_all_iff.mpr
  intro i
  have h : ∀ᵐ x ∂expMeasure 1, 0 < x := by
    apply (mem_ae_iff_prob_eq_one measurableSet_Ioi).mpr
    simpa using exponential_tail (t := 0) le_rfl
  rw [← rawLaw_eval i] at h
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Ioi).mp h

theorem rawLaw_independent : iIndepFun (fun i (z : Nat → ℝ) => z i) rawLaw := by
  exact iIndepFun_infinitePi (fun _ => measurable_id)

theorem rawLaw_large_independent : iIndepSet (fun i => {z : Nat → ℝ | 1 < z i}) rawLaw := by
  apply (iIndepSet_iff_meas_biInter (fun i => (measurable_pi_apply i) measurableSet_Ioi)).mpr
  intro s
  exact rawLaw_independent.meas_biInter (fun i _ => ⟨Ioi 1, measurableSet_Ioi, rfl⟩)

theorem rawLaw_large (i : Nat) : rawLaw {z | 1 < z i} = ENNReal.ofReal (Real.exp (-1)) := by
  have hh := Measure.map_apply (μ := rawLaw) (measurable_pi_apply i) (measurableSet_Ioi (a := (1 : ℝ)))
  rw [rawLaw_eval] at hh
  exact hh.symm.trans (exponential_tail (by norm_num))

def Good (z : Nat → ℝ) : Prop := (∀ i, 0 < z i) ∧ ∀ N, ∃ i, N ≤ i ∧ 1 < z i

theorem measurable_good : MeasurableSet {z | Good z} := by
  unfold Good
  measurability

theorem rawLaw_good : ∀ᵐ z ∂rawLaw, Good z := by
  have hm := measure_limsup_eq_one
    (fun i => measurableSet_lt measurable_const (measurable_pi_apply i)) rawLaw_large_independent
    (by simp only [rawLaw_large]; exact ENNReal.tsum_const_eq_top_of_ne_zero (by positivity))
  have ha : ∀ᵐ z ∂rawLaw, z ∈ limsup (fun i => {z : Nat → ℝ | 1 < z i}) atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup (fun i => measurableSet_lt measurable_const (measurable_pi_apply i)))).mpr hm
  filter_upwards [rawLaw_positive, ha] with z hz hlarge
  refine ⟨hz, ?_⟩
  simpa only [mem_limsup_iff_frequently_mem, frequently_atTop, Set.mem_setOf_eq] using hlarge

abbrev Clock := {z : Nat → ℝ // Good z}

noncomputable def law : Measure Clock := rawLaw.comap Subtype.val

theorem law_map : law.map Subtype.val = rawLaw := by
  have h : law.map Subtype.val = rawLaw.restrict {z | Good z} :=
    map_comap_subtype_coe measurable_good rawLaw
  exact h.trans (Measure.restrict_eq_self_of_ae_mem rawLaw_good)

instance : IsProbabilityMeasure law := by
  constructor
  have h : law Set.univ = rawLaw {z | Good z} := by
    have hh := comap_subtype_coe_apply measurable_good rawLaw (Set.univ : Set Clock)
    simpa only [Set.image_univ, Subtype.range_coe] using hh
  exact h.trans ((mem_ae_iff_prob_eq_one measurable_good).mp rawLaw_good)

theorem law_eval (i : Nat) : law.map (fun z : Clock => z.val i) = expMeasure 1 := by
  have h := Measure.map_map (measurable_pi_apply i) measurable_subtype_coe (μ := law)
  rw [law_map, rawLaw_eval] at h
  exact h.symm

theorem law_independent : iIndepFun (fun i (z : Clock) => z.val i) law := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (X := fun i (z : Clock) => z.val i) (P := law)
    (fun i => (measurable_pi_apply i).comp measurable_subtype_coe)).mpr
  change law.map Subtype.val = Measure.infinitePi _
  rw [law_map]
  unfold rawLaw
  congr 1
  funext i
  exact (law_eval i).symm

theorem law_tail (i : Nat) {t : ℝ} (ht : 0 ≤ t) :
    law {z | t < z.val i} = ENNReal.ofReal (Real.exp (-t)) := by
  have h := Measure.map_apply (μ := law) ((measurable_pi_apply i).comp measurable_subtype_coe) (measurableSet_Ioi (a := t))
  change (law.map (fun z : Clock => z.val i)) (Ioi t) = law {z | t < z.val i} at h
  rw [law_eval] at h
  exact h.symm.trans (exponential_tail ht)

theorem clock_positive (z : Clock) (i : Nat) : 0 < z.val i := z.property.1 i

theorem clock_diverges (z : Clock) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, z.val i) atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun i => (clock_positive z i).le)).mp
  intro hs
  have ht := hs.tendsto_atTop_zero
  have hsmall : ∀ᶠ i in atTop, z.val i < 1 := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  obtain ⟨i, hi, hlarge⟩ := z.property.2 N
  exact (not_lt_of_ge (hN i hi).le) hlarge

end OddCycle.ExponentialClock
