import OddCycle.Model
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring

namespace OddCycle

variable {K : Type*} [Field K]

/-- A change of normalization scales every balance equation by the same factor. -/
theorem balance_scale (adj : Nat → Nat → Bool) (budget : Nat) (rate : Nat → K)
    (states : List State) (weight : State → K) (target : State) (k : K) :
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

theorem Stationary.scale {adj : Nat → Nat → Bool} {budget : Nat} {rate : Nat → K}
    {states : List State} {weight : State → K}
    (h : Stationary adj budget rate states weight) (k : K) :
    Stationary adj budget rate states (fun s => k * weight s) := by
  intro t ht
  rw [balance_scale, h t ht, mul_zero]

end OddCycle
