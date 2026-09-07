import OddCycle.OrientationClasses
import OddCycle.ExceptionalCycleCommunication

namespace OddCycle

noncomputable def exceptionalStates (n w : Nat) : List State := by
  classical
  exact (allStates n).filter (fun s => decide (ExceptionalRuns n w s))

theorem mem_exceptionalStates {n w : Nat} {s : State} :
    s ∈ exceptionalStates n w ↔ Valid n s ∧ ExceptionalRuns n w s := by
  simp [exceptionalStates, mem_allStates_iff]

theorem exceptionalStates_support (n w : Nat) : OrientationSupport n (exceptionalStates n w) where
  nodup := (allStates_nodup n).filter _
  valid _ hs := (mem_exceptionalStates.mp hs).1
  fiber _ hs _ ht ho := by
    apply mem_exceptionalStates.mpr ⟨ht, ?_⟩
    have he := (mem_exceptionalStates.mp hs).2
    simpa only [ExceptionalRuns, cycleRuns, ho] using he

end OddCycle
