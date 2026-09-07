import OddCycle.ModulatedFiveJob
import OddCycle.AdditiveOI
import Mathlib.Algebra.BigOperators.Field

/-! The certified weights are the unique stationary law of the actual
two-mode generator. Nonfactorization allows environment-dependent factors. -/

namespace OddCycle.ModulatedFiveJob

noncomputable def allocation : PositiveOIAllocation 5 :=
  positiveAdditiveAllocation 5 (fun job => (jobRate job : ℝ)) (by
    intro job _
    have h : 0 < jobRate job := by unfold jobRate; split <;> decide
    exact Nat.cast_pos.mpr h)

theorem allocation_increment (q : Queue) (p : Nat) (hp : p < q.length) :
    allocation.toOICapacity.increment q p = (jobRate q[p] : ℝ) :=
  additive_increment _ q p hp

abbrev Supported := {s : JointState // s ∈ support}
instance : Nonempty Supported := ⟨⟨r₁₁, rectangle_mem.1⟩⟩

theorem supported_sum {R : Type*} [AddCommMonoid R] (f : JointState → R) :
    ∑ s : Supported, f s.val = (support.map f).sum := by
  rw [← Finset.sum_subtype support.toFinset (fun _ => List.mem_toFinset) f]
  exact List.sum_toFinset f support_nodup

theorem sum_event (e : JointState × Nat) (he : e.1 ∈ support) :
    (∑ t : Supported, if e.1 = t.val then e.2 else 0) = e.2 := by
  rw [Finset.sum_eq_single (⟨e.1, he⟩ : Supported)]
  · simp
  · intro t _ ht
    exact if_neg (fun h => ht (Subtype.ext h.symm))
  · simp

theorem incomingRate_sum (s : Supported) : ∑ t : Supported, incomingRate s.val t.val = 7 := by
  have he : ∀ es : List (JointState × Nat), (∀ e ∈ es, e.1 ∈ support) →
      (∑ t : Supported, (es.map (fun e => if e.1 = t.val then e.2 else 0)).sum) =
        (es.map Prod.snd).sum := by
    intro es
    induction es with
    | nil => intro _; simp
    | cons e es ih =>
      intro h
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [sum_event e (h e (List.mem_cons_self)),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
  unfold incomingRate
  rw [he _ (fun e he => support_closed s.val s.property e he)]
  exact total_event_rate s.val s.property

/-- Rate seven uniformization; every entry comes from the operational events. -/
noncomputable def kernel : FiniteMarkov Supported where
  prob s t := (incomingRate s.val t.val : ℝ) / 7
  nonneg s t := div_nonneg (Nat.cast_nonneg _) (by norm_num)
  sum_one s := by
    have h : (∑ t : Supported, (incomingRate s.val t.val : ℝ)) = 7 := by
      exact_mod_cast incomingRate_sum s
    simp only [div_eq_mul_inv, ← Finset.sum_mul, h]
    norm_num

theorem kernel_step (s t : Supported) (h : Step s.val t.val) : 0 < kernel.prob s t := by
  obtain ⟨rate, he, hp⟩ := h
  have hm : rate ∈ (modeEvents s.val).map (fun e => if e.1 = t.val then e.2 else 0) :=
    List.mem_map.mpr ⟨(t.val, rate), he, by simp⟩
  have hle : rate ≤ incomingRate s.val t.val :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ hm
  exact div_pos (Nat.cast_pos.mpr (hp.trans_le hle)) (by norm_num)

theorem kernel_irreducible : kernel.Irreducible := by
  intro s t
  have liftPath : ∀ {u : JointState}, Reachable s.val u →
      ∀ hu : u ∈ support, kernel.Reachable s ⟨u, hu⟩ := by
    intro u path
    induction path with
    | refl => intro _; exact .refl
    | @tail u v path step ih =>
      intro hv
      have hu := reachable_closed s.property path
      exact (ih hu).tail (kernel_step ⟨u, hu⟩ ⟨v, hv⟩ step)
  exact liftPath (communication s.property t.property) t.property

/-- Incoming weighted event rate minus the actual total outgoing rate. -/
noncomputable def generatorBalance (v : Supported → ℝ) (t : Supported) : ℝ :=
  (∑ s : Supported, v s * (incomingRate s.val t.val : ℝ)) - 7 * v t

def GeneratorStationary (v : Supported → ℝ) : Prop := ∀ t, generatorBalance v t = 0

theorem generatorBalance_eq (v : Supported → ℝ) (t : Supported) :
    generatorBalance v t = 7 * (kernel.advance v t - v t) := by
  change (∑ s : Supported, v s * (incomingRate s.val t.val : ℝ)) - 7 * v t =
    7 * ((∑ s : Supported, v s * ((incomingRate s.val t.val : ℝ) / 7)) - v t)
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  ring

theorem generator_stationary_iff (v : Supported → ℝ) :
    GeneratorStationary v ↔ kernel.StationaryVector v := by
  simp only [GeneratorStationary, generatorBalance_eq, FiniteMarkov.StationaryVector]
  constructor
  · intro h t
    have ht := h t
    have he : kernel.advance v t - v t = 0 := by linarith
    exact sub_eq_zero.mp he
  · intro h t
    rw [h t, sub_self, mul_zero]

noncomputable def probability (s : Supported) : ℝ := (integerWeight s.val : ℝ) / totalWeight

theorem probability_positive (s : Supported) : 0 < probability s :=
  div_pos (Nat.cast_pos.mpr (certificate_positive s.val s.property)) (by norm_num [totalWeight])

theorem probability_sum : ∑ s : Supported, probability s = 1 := by
  have hn : (∑ s : Supported, integerWeight s.val) = totalWeight := by
    rw [supported_sum]
    exact certificate_total
  have hsum : (∑ s : Supported, (integerWeight s.val : ℝ)) = totalWeight := by
    exact_mod_cast hn
  simp only [probability, ← Finset.sum_div, hsum]
  exact div_self (by norm_num [totalWeight])

theorem probability_simplex : probability ∈ stdSimplex ℝ Supported :=
  ⟨fun s => (probability_positive s).le, probability_sum⟩

theorem probability_stationary : kernel.StationaryVector probability := by
  intro t
  have hn : (∑ s : Supported, integerWeight s.val * incomingRate s.val t.val) =
      7 * integerWeight t.val := by
    rw [supported_sum (fun s => integerWeight s * incomingRate s t.val)]
    exact certificate_balance t.val t.property
  have hi : (∑ s : Supported, (integerWeight s.val : ℝ) * (incomingRate s.val t.val : ℝ)) =
      7 * (integerWeight t.val : ℝ) := by
    exact_mod_cast hn
  change (∑ s : Supported, ((integerWeight s.val : ℝ) / totalWeight) *
    ((incomingRate s.val t.val : ℝ) / 7)) = (integerWeight t.val : ℝ) / totalWeight
  simp only [div_mul_div_comm, ← Finset.sum_div, hi]
  field_simp

theorem probability_generator_stationary : GeneratorStationary probability :=
  (generator_stationary_iff probability).mpr probability_stationary

theorem probability_unique {v : Supported → ℝ} (hv : v ∈ stdSimplex ℝ Supported)
    (hs : GeneratorStationary v) : v = probability :=
  kernel.stationary_unique kernel_irreducible hv probability_simplex
    ((generator_stationary_iff v).mp hs) probability_stationary

theorem stationary_not_product {v : Supported → ℝ} (hv : v ∈ stdSimplex ℝ Supported)
    (hs : GeneratorStationary v) :
    ¬ ∃ (K : Bool → ℝ) (A B : Bool → Queue → ℝ), ∀ s : Supported,
      v s = K s.val.2 * A s.val.2 s.val.1.1 * B s.val.2 s.val.1.2 := by
  rw [probability_unique hv hs]
  rintro ⟨K, A, B, h⟩
  apply normalized_certificate_not_product (totalWeight : ℝ) (by norm_num [totalWeight])
  exact ⟨K, A, B, fun s hs => h ⟨s, hs⟩⟩

end OddCycle.ModulatedFiveJob
