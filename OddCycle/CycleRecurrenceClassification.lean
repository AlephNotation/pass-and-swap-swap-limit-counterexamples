import OddCycle.FiniteAbsorption
import OddCycle.ExceptionalCycleCount

/-! The probabilistic recurrence and absorption classification for kernels
supported on the original queue completion events. -/

namespace OddCycle.CycleState

open Filter Topology

variable {n w : Nat} (P : FiniteMarkov (CycleState n))
variable (hsupport : ∀ s t, 0 < P.prob s t → Step n w s t ∨ s = t)
variable (hpositive : ∀ s t, Step n w s t → 0 < P.prob s t)

include hsupport hpositive

theorem kernel_reachable_iff (s t : CycleState n) :
    P.Reachable s t ↔ Relation.ReflTransGen (Step n w) s t := by
  constructor
  · exact Relation.ReflTransGen.lift' id (fun a b hab => by
      rcases hsupport a b hab with h | rfl
      · exact .single h
      · exact .refl)
  · exact Relation.ReflTransGen.lift id (fun a b hab => hpositive a b hab)

theorem kernel_terminal_iff (s : CycleState n) :
    ReachabilityQuotient.Terminal (fun a b => 0 < P.prob a b) s ↔
      ReachabilityQuotient.Terminal (Step n w) s := by
  change (∀ t, P.Reachable s t → P.Reachable t s) ↔
    (∀ t, Relation.ReflTransGen (Step n w) s t → Relation.ReflTransGen (Step n w) t s)
  simp only [kernel_reachable_iff P hsupport hpositive]

theorem recurrent_iff_runs (hn : 3 ≤ n) (hw : 1 ≤ w) (s : CycleState n) :
    Tendsto (P.returnBy s) atTop (𝓝 1) ↔ ShortRuns n w s.val ∨ ExceptionalRuns n w s.val := by
  rw [P.returnBy_tendsto_one_iff_terminal, kernel_terminal_iff P hsupport hpositive,
    terminal_iff_runs hn hw]

theorem transient_iff_runs (hn : 3 ≤ n) (hw : 1 ≤ w) (s : CycleState n) :
    ¬ Tendsto (P.returnBy s) atTop (𝓝 1) ↔
      ¬ ShortRuns n w s.val ∧ ¬ ExceptionalRuns n w s.val := by
  rw [recurrent_iff_runs P hsupport hpositive hn hw, not_or]

attribute [local instance] Classical.propDecidable

theorem classified_avoid_tendsto_zero (hn : 3 ≤ n) (hw : 1 ≤ w) (s : CycleState n) :
    Tendsto (fun j => P.avoidSet
      (fun t => ShortRuns n w t.val ∨ ExceptionalRuns n w t.val) j s) atTop (𝓝 0) := by
  have he : (fun t => ShortRuns n w t.val ∨ ExceptionalRuns n w t.val) =
      ReachabilityQuotient.Terminal (fun a b => 0 < P.prob a b) := by
    funext t
    exact propext ((kernel_terminal_iff P hsupport hpositive t).trans (terminal_iff_runs hn hw t)).symm
  simpa only [he] using P.avoid_terminal_tendsto_zero s

theorem short_avoid_tendsto_zero (hn : 3 ≤ n) (hw : 1 ≤ w)
    (hlength : ¬ ∃ k, 1 ≤ k ∧ n = 2 * k * w + 1) (s : CycleState n) :
    Tendsto (fun j => P.avoidSet (fun t => ShortRuns n w t.val) j s) atTop (𝓝 0) := by
  have he : (fun t : CycleState n => ShortRuns n w t.val ∨ ExceptionalRuns n w t.val) =
      (fun t => ShortRuns n w t.val) := by
    funext t
    apply propext
    constructor
    · intro h
      exact terminal_short_of_nonexceptional_length hn hw hlength t ((terminal_iff_runs hn hw t).mpr h)
    · exact Or.inl
  simpa only [he] using classified_avoid_tendsto_zero P hsupport hpositive hn hw s

omit hpositive in
theorem exceptional_recurrent_state {k : Nat} (hn : n = 2 * k * w + 1)
    (hw : 1 ≤ w) (hk : 1 ≤ k) :
    ∃ s : CycleState n, ExceptionalRuns n w s.val ∧ w < height n s.val ∧
      Tendsto (P.returnBy s) atTop (𝓝 1) := by
  have hn3 : 3 ≤ n := by nlinarith
  let A : CycleState n → Prop := fun s => ExceptionalRuns n w s.val
  have hc : ∀ s, A s → ∀ t, ¬ A t → P.prob s t = 0 := by
    intro s hs t ht
    apply le_antisymm _ (P.nonneg s t)
    by_contra h
    rcases hsupport s t (lt_of_not_ge h) with ⟨side, pos, init, he⟩ | he
    · exact ht (exceptionalRuns_transition hn3 hw s.property hs he)
    · exact ht (he ▸ hs)
  obtain ⟨s, hs, hex⟩ := exceptionalRuns_exists hw hk hn
  obtain ⟨t, ht, hr⟩ := P.closed_recurrent_state_exists A hc ⟨⟨s, hs⟩, hex⟩
  exact ⟨t, ht, exceptionalRuns_tall hn3 t.property ht, hr⟩

end OddCycle.CycleState
