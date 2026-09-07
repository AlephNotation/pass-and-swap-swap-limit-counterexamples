import OddCycle.OICapacity
import Mathlib.Tactic.Ring

/-! Exact partial balance for an unlimited pass-and-swap queue. Reversing
the scan gives every predecessor, and adjacent insertion positions telescope. -/

namespace OddCycle

variable {K : Type*} [Field K]

theorem reverseInput_prefix (adj : Nat → Nat → Bool) (pre rest : Queue) (d : Nat) :
    reverseInput adj (pre ++ rest) d pre.length =
      pre ++ (unlimitedCarry adj d rest.reverse).2 :: (unlimitedCarry adj d rest.reverse).1.reverse := by
  simp [reverseInput]

theorem reverseInput_prefix_succ (adj : Nat → Nat → Bool) (pre tail : Queue) (a d : Nat) :
    reverseInput adj (pre ++ a :: tail) d (pre.length + 1) =
      pre ++ a :: (unlimitedCarry adj d tail.reverse).2 :: (unlimitedCarry adj d tail.reverse).1.reverse := by
  have hh := reverseInput_prefix adj (pre ++ [a]) tail d
  simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] using hh

theorem reverseInput_take (adj : Nat → Nat → Bool) (rest : Queue) (d p : Nat)
    (hp : p ≤ rest.length) : (reverseInput adj rest d p).take p = rest.take p := by
  simp only [reverseInput, List.take_append, List.take_take, Nat.min_self,
    List.length_take, Nat.min_eq_left hp, Nat.sub_self, List.take_zero, List.append_nil]

theorem reverseInput_take_succ (adj : Nat → Nat → Bool) (rest : Queue) (d p : Nat)
    (hp : p ≤ rest.length) :
    (reverseInput adj rest d p).take (p + 1) =
      rest.take p ++ [(unlimitedCarry adj d (rest.drop p).reverse).2] := by
  simp only [reverseInput, List.take_append, List.take_take, Nat.min_eq_right (by omega : p ≤ p + 1),
    List.length_take, Nat.min_eq_left hp, Nat.add_sub_cancel_left, List.take_succ_cons, List.take_zero]

namespace OICapacity

theorem reverse_adjacent (μ : OICapacity K) (adj : Nat → Nat → Bool)
    (pre tail : Queue) (a d : Nat) (hr : μ.Regular ((pre ++ a :: tail) ++ [d])) :
    μ.weight (reverseInput adj (pre ++ a :: tail) d pre.length) *
      μ ((reverseInput adj (pre ++ a :: tail) d pre.length).take (pre.length + 1)) =
    μ.weight (reverseInput adj (pre ++ a :: tail) d (pre.length + 1)) * μ (pre ++ [a]) := by
  let back := unlimitedCarry adj d tail.reverse
  have hn := hr.perm (reverseInput_perm (adj := adj) (pre ++ a :: tail) d (pre.length + 1)).symm
  rw [reverseInput_prefix_succ] at hn
  change μ.Regular (pre ++ a :: back.2 :: back.1.reverse) at hn
  have ha : μ (pre ++ [a]) ≠ 0 := hn _
    (((List.prefix_append [a] (back.2 :: back.1.reverse)).sublist.append_left pre).subperm) (by simp)
  have hb : μ (pre ++ [back.2]) ≠ 0 := by
    have hp : (pre ++ back.2 :: a :: back.1.reverse).Perm (pre ++ a :: back.2 :: back.1.reverse) :=
      (List.Perm.swap a back.2 back.1.reverse).append_left pre
    exact hn _
      ((((List.prefix_append [back.2] (a :: back.1.reverse)).sublist.append_left pre).subperm).trans hp.subperm)
      (by simp)
  rw [reverseInput_take_succ adj _ _ _ (by simp), reverseInput_prefix, reverseInput_prefix_succ]
  simp only [List.take_left, List.drop_left, List.reverse_cons, unlimitedCarry_append]
  change μ.weight (pre ++ (unlimitedCarry adj back.2 [a]).2 ::
      (back.1 ++ (unlimitedCarry adj back.2 [a]).1).reverse) *
    μ (pre ++ [(unlimitedCarry adj back.2 [a]).2]) =
      μ.weight (pre ++ a :: back.2 :: back.1.reverse) * μ (pre ++ [a])
  by_cases h : adj back.2 a = true
  · simp [unlimitedCarry, h]
  · simpa [unlimitedCarry, h, List.append_assoc] using μ.weight_swap pre back.1.reverse back.2 a hb ha

theorem reverse_adjacent_at (μ : OICapacity K) (adj : Nat → Nat → Bool)
    (rest : Queue) (d p : Nat) (hp : p < rest.length) (hr : μ.Regular (rest ++ [d])) :
    μ.weight (reverseInput adj rest d p) * μ ((reverseInput adj rest d p).take (p + 1)) =
      μ.weight (reverseInput adj rest d (p + 1)) * μ (rest.take (p + 1)) := by
  have hsplit : rest.take p ++ rest[p] :: rest.drop (p + 1) = rest := by
    have hh := List.take_append_drop (p + 1) rest
    rw [List.take_succ_eq_append_getElem hp, List.append_assoc, List.singleton_append] at hh
    exact hh
  have hh := μ.reverse_adjacent adj (rest.take p) (rest.drop (p + 1)) rest[p] d
    (by simpa only [hsplit] using hr)
  simpa only [hsplit, List.length_take, Nat.min_eq_left hp.le,
    ← List.take_succ_eq_append_getElem hp] using hh

theorem unlimited_partial_balance (μ : OICapacity K) (adj : Nat → Nat → Bool)
    (rest : Queue) (d : Nat) (hr : μ.Regular (rest ++ [d])) :
    ((List.range (rest.length + 1)).map (fun p =>
      μ.weight (reverseInput adj rest d p) * μ.increment (reverseInput adj rest d p) p)).sum =
        μ.weight rest := by
  let A := fun p => μ.weight (reverseInput adj rest d p) * μ (rest.take p)
  have hstep (p : Nat) (hp : p < rest.length) :
      μ.weight (reverseInput adj rest d p) * μ.increment (reverseInput adj rest d p) p = A (p + 1) - A p := by
    rw [increment, mul_sub, μ.reverse_adjacent_at adj rest d p hp hr,
      reverseInput_take adj rest d p hp.le]
  have hsum (k : Nat) (hk : k ≤ rest.length) :
      ((List.range k).map (fun p => μ.weight (reverseInput adj rest d p) *
        μ.increment (reverseInput adj rest d p) p)).sum = A k := by
    induction k with
    | zero => simp [A, μ.empty]
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        hstep k (by omega)]
      ring
  rw [List.range_succ, List.map_append, List.sum_append, hsum rest.length le_rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have hlast : reverseInput adj rest d rest.length = rest ++ [d] := by
    simp [reverseInput, unlimitedCarry]
  have hne : μ (rest ++ [d]) ≠ 0 := hr _ (List.Subperm.refl _) (by simp)
  have ht0 : (rest ++ [d]).take rest.length = rest := by simp
  have ht1 : (rest ++ [d]).take (rest.length + 1) = rest ++ [d] := by
    simp
  simp only [A, hlast, increment, ht0, ht1, List.take_length, μ.weight_append_singleton]
  field_simp
  ring

end OICapacity
end OddCycle
