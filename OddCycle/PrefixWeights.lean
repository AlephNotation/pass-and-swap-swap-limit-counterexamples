import OddCycle.PlacementOrder
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring

/-! Symbolic prefix-product weights over arbitrary fields. -/

namespace OddCycle

variable {K : Type*} [Field K]

def spikeRate (theta : K) (job : Nat) : K := if job = 0 then theta else 1

theorem prefixWeight_append (rate : Nat → K) (total : K) (a b : Queue) :
    prefixWeight rate total (a ++ b) =
      prefixWeight rate total a * prefixWeight rate (total + (a.map rate).sum) b := by
  induction a generalizing total with
  | nil => simp [prefixWeight]
  | cons x xs ih => simp [prefixWeight, ih, add_assoc, mul_assoc]

theorem sum_unit_rates (rate : Nat → K) (q : Queue) (hr : ∀ x ∈ q, rate x = 1) :
    (q.map rate).sum = (q.length : K) := by
  induction q with
  | nil => simp
  | cons x xs ih =>
    simp [hr x (by simp), ih (fun y hy => hr y (by simp [hy])), add_comm]

theorem prefixWeight_unit (rate : Nat → K) (q : Queue) (hr : ∀ x ∈ q, rate x = 1) :
    prefixWeight rate 0 q = (q.length.factorial : K)⁻¹ := by
  induction q using List.reverseRecOn with
  | nil => simp [prefixWeight]
  | append_singleton q x ih =>
    have hx := hr x (by simp)
    have hq : ∀ y ∈ q, rate y = 1 := fun y hy => hr y (by simp [hy])
    rw [prefixWeight_append, ih hq, sum_unit_rates rate q hq]
    simp [prefixWeight, hx, Nat.factorial_succ, mul_comm]

theorem prefixWeight_unit_shift (rate : Nat → K) (total : K) (q : Queue) (hr : ∀ x ∈ q, rate x = 1) :
    prefixWeight rate total q =
      (((List.range q.length).map (fun j => total + (j + 1 : Nat))).prod)⁻¹ := by
  induction q using List.reverseRecOn with
  | nil => simp [prefixWeight]
  | append_singleton q x ih =>
    have hx := hr x (by simp)
    have hq : ∀ y ∈ q, rate y = 1 := fun y hy => hr y (by simp [hy])
    rw [prefixWeight_append, ih hq, sum_unit_rates rate q hq]
    simp [prefixWeight, hx, List.range_succ, mul_comm, add_assoc]

theorem prefixWeight_spike_last (theta : K) (q : Queue) (hq : 0 ∉ q) :
    prefixWeight (spikeRate theta) 0 (q ++ [0]) =
      (q.length.factorial : K)⁻¹ * (theta + q.length)⁻¹ := by
  have hu : ∀ x ∈ q, spikeRate theta x = 1 := by
    intro x hx
    have hne : x ≠ 0 := by intro he; subst x; exact hq hx
    simp [spikeRate, hne]
  rw [prefixWeight_append, prefixWeight_unit _ q hu, sum_unit_rates _ q hu]
  simp [prefixWeight, spikeRate, add_comm]

theorem prefixWeight_spike_first (theta : K) (q : Queue) :
    prefixWeight (spikeRate theta) 0 (0 :: q) = theta⁻¹ * prefixWeight (spikeRate theta) theta q := by
  simp [prefixWeight, spikeRate]

theorem prefixWeight_spike_between (theta : K) (a b : Queue) (ha : 0 ∉ a) (hb : 0 ∉ b) :
    prefixWeight (spikeRate theta) 0 (a ++ 0 :: b) =
      (a.length.factorial : K)⁻¹ *
        (((List.range (b.length + 1)).map (fun j : Nat => theta + (a.length : K) + (j : K))).prod)⁻¹ := by
  have hu (q : Queue) (hq : 0 ∉ q) : ∀ x ∈ q, spikeRate theta x = 1 := by
    intro x hx
    have hn : x ≠ 0 := by intro he; subst x; exact hq hx
    simp [spikeRate, hn]
  rw [prefixWeight_append, prefixWeight_unit _ a (hu a ha), sum_unit_rates _ a (hu a ha)]
  simp only [prefixWeight, spikeRate, ↓reduceIte, zero_add]
  rw [prefixWeight_unit_shift _ _ b (hu b hb)]
  simp [List.range_succ_eq_map, List.map_map, Function.comp_def, add_assoc, add_comm, add_left_comm,
    mul_comm, mul_left_comm]

/-- The nonzero labels may occur in any order. -/
theorem spike_last_weight_of_valid {n : Nat} (theta : K) {q : Queue}
    (hv : Valid (n + 1) (q, [])) (hends : ∃ pre, q = pre ++ [0]) :
    canonicalWeight (spikeRate theta) ([], q) = (n.factorial : K)⁻¹ * (theta + n)⁻¹ := by
  obtain ⟨pre, rfl⟩ := hends
  have hlen := hv.length_eq
  simp only [List.length_append, List.length_singleton, List.length_nil, Nat.add_zero, List.length_range] at hlen
  have hp : pre.length = n := by omega
  have hnd := hv.placement_nodup
  simp only [placement, List.reverse_nil, List.append_nil] at hnd
  have hzero : 0 ∉ pre := by
    intro hm
    exact (List.nodup_append.mp hnd).2.2 0 hm 0 (by simp) rfl
  simp [canonicalWeight, prefixWeight, prefixWeight_spike_last theta pre hzero, hp]

end OddCycle
