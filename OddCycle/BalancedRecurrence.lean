import OddCycle.ClosedRecurrence
import OddCycle.QueueStationary
import OddCycle.GeneralHeight
import OddCycle.PartiteColoring

/-! The recurrence obstruction for every finite completion kernel. -/

namespace OddCycle

abbrev PopulationState (n : Nat) := {s : State // s ∈ allStates n}

/-- Any stochastic allocation supported on legal completions (with optional
self steps) has a recurrent balanced state of height w+1. No irreducibility
or positivity assumption on individual completion positions is needed. -/
theorem balanced_recurrent_state {w : Nat} (hw : 2 ≤ w)
    (P : FiniteMarkov (PopulationState (2 * w + 1)))
    (hsupport : ∀ s t, 0 < P.prob s t →
      EventStep (cycleAdjacent (2 * w + 1)) w s.val t.val ∨ s = t) :
    ∃ s : PopulationState (2 * w + 1), balanced w s.val = true ∧
      height (2 * w + 1) s.val = w + 1 ∧
      Filter.Tendsto (P.returnBy s) Filter.atTop (nhds 1) := by
  let A : PopulationState (2 * w + 1) → Prop := fun s => balanced w s.val = true
  have hc : ∀ s, A s → ∀ t, ¬ A t → P.prob s t = 0 := by
    intro s hs t ht
    apply le_antisymm _ (P.nonneg s t)
    by_contra hn
    rcases hsupport s t (lt_of_not_ge hn) with he | he
    · obtain ⟨side, pos, init, htr⟩ := he
      exact ht (balanced_transition hw (mem_allStates_iff.mp s.property) hs htr)
    · exact ht (he ▸ hs)
  have hne : ∃ s, A s := by
    let s := branchState w 0 true
    have hv := branchState_valid hw (by omega : 0 < 2 * w + 1) true
    exact ⟨⟨s, mem_allStates_iff.mpr hv⟩, branchState_balanced (by omega : 0 < 2 * w + 1) true⟩
  obtain ⟨s, hs, hr⟩ := P.closed_recurrent_state_exists A hc hne
  exact ⟨s, hs, balanced_height hw (mem_allStates_iff.mp s.property) hs, hr⟩

end OddCycle
