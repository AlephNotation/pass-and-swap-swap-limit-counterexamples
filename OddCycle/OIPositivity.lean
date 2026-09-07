import OddCycle.OICapacity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace OddCycle

namespace OICapacity

variable {K : Type*} [Field K]

theorem sum_increments (μ : OICapacity K) (q : Queue) :
    ((List.range q.length).map (μ.increment q)).sum = μ q := by
  have h (k : Nat) : ((List.range k).map (μ.increment q)).sum = μ (q.take k) := by
    induction k with
    | zero => simp [μ.empty]
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, increment]
      ring
  simpa using h q.length

end OICapacity

namespace PositiveOIAllocation

theorem capacity_pos {n : Nat} (μ : PositiveOIAllocation n) {q : Queue}
    (hq : q.Subperm (List.range n)) (hne : q ≠ []) : 0 < μ.value q := by
  rw [← μ.toOICapacity.sum_increments]
  apply List.sum_pos
  · intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact μ.positive q hq p (List.mem_range.mp hp)
  · simpa using (List.length_pos_iff.mpr hne).ne'

theorem regular {n : Nat} (μ : PositiveOIAllocation n) : μ.toOICapacity.Regular (List.range n) :=
  fun _ hq hne => (μ.capacity_pos hq hne).ne'

theorem prefixProduct_pos {n : Nat} (μ : PositiveOIAllocation n) (pre tail : Queue)
    (h : (pre ++ tail).Subperm (List.range n)) : 0 < μ.toOICapacity.prefixProduct pre tail := by
  induction tail generalizing pre with
  | nil => exact zero_lt_one
  | cons x xs ih =>
    rw [OICapacity.prefixProduct]
    apply mul_pos
    · apply inv_pos.mpr
      apply μ.capacity_pos _ (by simp)
      exact ((List.prefix_append [x] xs).sublist.append_left pre).subperm.trans h
    · apply ih
      simpa only [List.append_assoc, List.singleton_append] using h

theorem weight_pos {n : Nat} (μ : PositiveOIAllocation n) {q : Queue}
    (h : q.Subperm (List.range n)) : 0 < μ.toOICapacity.weight q :=
  μ.prefixProduct_pos [] q (by simpa only [List.nil_append] using h)

end PositiveOIAllocation
end OddCycle
