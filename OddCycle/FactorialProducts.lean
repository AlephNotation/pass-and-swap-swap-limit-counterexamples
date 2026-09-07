import OddCycle.UniformWeights
import Mathlib.Tactic.FieldSimp

/-! Finite consecutive products and the factorial specialization at theta = 2. -/

namespace OddCycle

variable {K : Type*} [Field K]

theorem factorial_mul_range_product (m count : Nat) :
    (m.factorial : K) * ((List.range count).map (fun j : Nat => ((m + j + 1 : Nat) : K))).prod =
      ((m + count).factorial : K) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [← mul_assoc, ih]
    rw [show m + (count + 1) = (m + count) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring

theorem shiftedProduct_two_factorial (w : Nat) :
    ((w + 1).factorial : K) * shiftedProduct w (2 : K) = ((2 * w + 2).factorial : K) := by
  have he : shiftedProduct w (2 : K) =
      ((List.range (w + 1)).map (fun j : Nat => (((w + 1) + j + 1 : Nat) : K))).prod := by
    unfold shiftedProduct
    apply congrArg List.prod
    apply List.map_congr_left
    intro j _
    push_cast
    ring
  rw [he, factorial_mul_range_product]
  congr 2
  omega

theorem flowSourceX_weight_two [CharZero K] {w : Nat} (hw : 2 ≤ w) :
    canonicalWeight (spikeRate (2 : K)) (flowSourceX w) = (w + 1 : Nat) / ((2 * w + 2).factorial : K) := by
  rw [flowSourceX_weight hw]
  have he := shiftedProduct_two_factorial (K := K) w
  have hn : (((2 * w + 2).factorial : Nat) : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hp : shiftedProduct w (2 : K) ≠ 0 := by intro hz; rw [hz, mul_zero] at he; exact hn he.symm
  have hf : (w.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [Nat.factorial_succ] at he
  push_cast at he
  field_simp
  rw [← he]
  push_cast
  ring

theorem flowSourceY_weight_two [CharZero K] {w : Nat} (hw : 2 ≤ w) :
    canonicalWeight (spikeRate (2 : K)) (flowSourceY w) = (2 * w + 1 : Nat) / ((2 * w + 2).factorial : K) := by
  rw [flowSourceY_weight hw]
  have hn : (((2 * w + 2).factorial : Nat) : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hf : (((2 * w).factorial : Nat) : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hp : (2 : K) + (2 * w : Nat) ≠ 0 := by
    have hnat : (((2 * w + 2 : Nat)) : K) ≠ 0 := by exact_mod_cast (show 2 * w + 2 ≠ 0 by omega)
    simpa [add_comm] using hnat
  have he : (((2 * w + 2).factorial : Nat) : K) =
      ((2 * w + 2 : Nat) : K) * (((2 * w + 1 : Nat) : K) * (((2 * w).factorial : Nat) : K)) := by
    rw [show 2 * w + 2 = (2 * w + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    rfl
  field_simp
  rw [he]
  push_cast
  ring

end OddCycle
