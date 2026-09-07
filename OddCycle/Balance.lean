import OddCycle.Model
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring

namespace OddCycle

/-- A change of normalization scales every balance equation by the same factor. -/
theorem balance_scale (adj : Nat → Nat → Bool) (budget : Nat) (rate : Nat → ℚ)
    (states : List State) (weight : State → ℚ) (target : State) (k : ℚ) :
    balance adj budget rate states (fun s => k * weight s) target =
      k * balance adj budget rate states weight target := by
  unfold balance
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  split_ifs <;> ring

theorem Stationary.scale {adj : Nat → Nat → Bool} {budget : Nat} {rate : Nat → ℚ}
    {states : List State} {weight : State → ℚ}
    (h : Stationary adj budget rate states weight) (k : ℚ) :
    Stationary adj budget rate states (fun s => k * weight s) := by
  intro t ht
  rw [balance_scale, h t ht, mul_zero]

end OddCycle
