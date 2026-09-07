import OddCycle.OrientationClasses

namespace OddCycle

theorem exceptional_length_iff_mod {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w) :
    (∃ k, 1 ≤ k ∧ n = 2 * k * w + 1) ↔ n % (2 * w) = 1 := by
  constructor
  · rintro ⟨k, _, rfl⟩
    rw [show 2 * k * w = (2 * w) * k by ring]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < 2 * w)]
  · intro h
    have he := Nat.mod_add_div n (2 * w)
    rw [h] at he
    have hk : 1 ≤ n / (2 * w) := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hz
      rw [hz, mul_zero, add_zero] at he
      omega
    exact ⟨n / (2 * w), hk, by nlinarith⟩

theorem safe_congruence_oi_stationary {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w)
    (hmod : n % (2 * w) ≠ 1) (μ ν : PositiveOIAllocation n) (s : CycleState n)
    (ht : ReachabilityQuotient.Terminal (CycleState.Step n w) s) :
    OIStationary (cycleAdjacent n) w μ.toOICapacity ν.toOICapacity
      (orientationStates n (orientation n s.val)) (oiCanonicalWeight μ.toOICapacity ν.toOICapacity) :=
  nonexceptional_recurrent_oi_stationary hn hw (fun h => hmod ((exceptional_length_iff_mod hn hw).mp h)) μ ν s ht

end OddCycle
