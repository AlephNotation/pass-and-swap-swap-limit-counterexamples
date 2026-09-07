import OddCycle.LengthStationary
import OddCycle.UnitExceptionalFailure

/-! An arbitrary-size family where the canonical law fails full stationarity
while satisfying every balance test that observes only queue length. -/

noncomputable section

namespace OddCycle

private theorem capacity_ext {μ ν : OICapacity ℝ} (h : μ.value = ν.value) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

theorem unitAllocation_byLength (n : Nat) :
    (unitAllocation n).toOICapacity = byLengthCapacity (fun k => (k : ℝ)) (by simp) := by
  exact capacity_ext (funext (fun q => unit_capacity q))

theorem unit_exceptional_hidden_defect {n w k : Nat}
    (hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1) :
    let μ := (unitAllocation n).toOICapacity
    let states := exceptionalStates n w
    let W := oiCanonicalWeight μ μ
    (¬ OIStationary (cycleAdjacent n) w μ μ states W) ∧
      ∀ f : Nat → ℝ, (∑ s : ↥states.toFinset,
        W s.val * lengthGenerator (cycleAdjacent n) w (fun _ => 1) (fun _ => 1) s.val f) = 0 := by
  refine ⟨unit_exceptional_not_stationary hw hk hn, ?_⟩
  intro f
  have h := (exceptionalStates_closedClass hw (by omega : 1 ≤ k) hn).canonical_length_observables
    (fun j => (j : ℝ)) (fun j => (j : ℝ)) (by simp) (by simp)
    (fun j hj _ => by change (j : ℝ) ≠ 0; exact_mod_cast (by omega : j ≠ 0))
    (fun j hj _ => by change (j : ℝ) ≠ 0; exact_mod_cast (by omega : j ≠ 0)) f
  rw [unitAllocation_byLength]
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left] using h

end OddCycle
