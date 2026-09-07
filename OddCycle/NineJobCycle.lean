import OddCycle.UnitExceptionalFailure
import OddCycle.ClosedClasses

/-! The author's requested explicit unit-rate example on C9, with w=2.
Its balance equation is a specialization of the arbitrary-size proof. -/

namespace OddCycle.NineJobCycle

def target : State := ([0], [7, 8, 6, 3, 4, 5, 2, 1])
def gained : State := ([], [7, 8, 0, 6, 3, 4, 5, 2, 1])

theorem interior : unitInterior 9 2 2 = [6] := by
  have hp : (unitInterior 9 2 2).Perm [6] := unitInterior_perm (by omega) (by omega) rfl
  exact List.perm_singleton.mp hp

theorem target_eq : unitPatternTarget 9 2 (unitInterior 9 2 2).reverse = target := by
  rw [interior]
  rfl

theorem gained_eq : (unitGainOccurrence 9 2 (unitInterior 9 2 2).reverse).source = gained := by
  rw [interior]
  decide +kernel

theorem target_member : target ∈ exceptionalStates 9 2 := by
  rw [← target_eq]
  exact mem_exceptionalStates.mpr ⟨unitPatternTarget_valid (by omega) (unitInterior_perm (by omega) (by omega) rfl),
    unit_target_exceptional (by omega) (by omega) rfl⟩

theorem recurrent_class : ClosedClass 9 2 (exceptionalStates 9 2) :=
  exceptionalStates_closedClass (k := 2) (by omega) (by omega) rfl

theorem gained_event : transition (cycleAdjacent 9) 2 gained true 0 = some (target, 7) := by decide +kernel

theorem residual : oiBalance (cycleAdjacent 9) 2 (unitAllocation 9).toOICapacity (unitAllocation 9).toOICapacity
    (exceptionalStates 9 2) (oiCanonicalWeight (unitAllocation 9).toOICapacity (unitAllocation 9).toOICapacity)
    target = -1 / 120960 := by
  have h := unit_exceptional_residual (n := 9) (w := 2) (k := 2) (by omega) (by omega) rfl
  rw [target_eq] at h
  norm_num [Nat.factorial] at h ⊢
  exact h

end OddCycle.NineJobCycle
