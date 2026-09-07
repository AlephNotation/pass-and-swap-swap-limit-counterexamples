import OddCycle.CycleLocalMoves
import OddCycle.OrientationRealization
import OddCycle.TerminalRecurrence

/-! Terminal components of the original queue-event graph, obtained from
the exact operational local-move theorem and the circular binary graph. -/

namespace OddCycle

namespace CycleState

def binaryProject {n : Nat} (hn : 3 ≤ n) (s : CycleState n) : BinaryCycle n :=
  ⟨orientation n s.val, orientation_length n s.val, orientation_nonconstant (by omega) s.property⟩

theorem binaryProject_surjective {n : Nat} (hn : 3 ≤ n) : Function.Surjective (binaryProject hn) := by
  intro q
  obtain ⟨s, hs, ho⟩ := orientation_surjective q.property.1 q.property.2
  exact ⟨⟨s, hs⟩, Subtype.ext ho⟩

theorem binary_step_orientationStep {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w)
    {a b : BinaryCycle n} (h : BinaryCycle.Step n w a b) : OrientationStep n w a.val b.val := by
  obtain ⟨s, hs, hsa⟩ := orientation_surjective a.property.1 a.property.2
  obtain ⟨t, ht, htb⟩ := orientation_surjective b.property.1 b.property.2
  have he := (orientationStep_iff_circularFlip hn hw hs ht).mpr
    (by simpa only [hsa, htb] using h)
  simpa only [hsa, htb] using he.1

theorem reachable_iff_binary {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w) (s t : CycleState n) :
    EventReachable (cycleAdjacent n) w s.val t.val ↔
      Relation.ReflTransGen (BinaryCycle.Step n w) (binaryProject hn s) (binaryProject hn t) := by
  constructor
  · intro h
    have hr := event_reachable_iff.mpr h
    apply Relation.ReflTransGen.lift' (binaryProject hn) ?_ hr
    intro a b hab
    obtain ⟨side, pos, initiating, he⟩ := hab
    by_cases ho : orientation n a.val = orientation n b.val
    · have hp : binaryProject hn a = binaryProject hn b := Subtype.ext ho
      rw [hp]
    · exact .single ((transition_pathFlip hn hw a.property he ho).circularFlip hn a.property b.property)
  · intro h
    apply orientation_reachable_iff.mpr
    exact Relation.ReflTransGen.lift Subtype.val
      (fun _ _ hs => binary_step_orientationStep hn hw hs) h

theorem terminal_iff_binary {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w) (s : CycleState n) :
    ReachabilityQuotient.Terminal (Step n w) s ↔
      ReachabilityQuotient.Terminal (BinaryCycle.Step n w) (binaryProject hn s) := by
  constructor
  · intro ht q hq
    obtain ⟨t, rfl⟩ := binaryProject_surjective hn q
    have hst := event_reachable_iff.mpr ((reachable_iff_binary hn hw s t).mpr hq)
    exact (reachable_iff_binary hn hw t s).mp (event_reachable_iff.mp (ht t hst))
  · intro ht t hst
    have hq := (reachable_iff_binary hn hw s t).mp (event_reachable_iff.mp hst)
    exact event_reachable_iff.mpr ((reachable_iff_binary hn hw t s).mpr (ht _ hq))

/-- The complete terminal-state test for actual queue configurations.
The definitions of `Step`, `ShortRuns`, and `ExceptionalRuns` are independent;
the equivalence follows from the operational scan and run-dynamics proofs. -/
theorem terminal_iff_runs {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w) (s : CycleState n) :
    ReachabilityQuotient.Terminal (Step n w) s ↔ ShortRuns n w s.val ∨ ExceptionalRuns n w s.val := by
  rw [terminal_iff_binary hn hw s, BinaryCycle.terminal_iff hw]
  rfl

theorem exceptional_terminal {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w) (s : CycleState n)
    (hs : ExceptionalRuns n w s.val) : ReachabilityQuotient.Terminal (Step n w) s :=
  (terminal_iff_runs hn hw s).mpr (Or.inr hs)

theorem terminal_short_of_nonexceptional_length {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w)
    (hlength : ¬ ∃ k, 1 ≤ k ∧ n = 2 * k * w + 1) (s : CycleState n)
    (hs : ReachabilityQuotient.Terminal (Step n w) s) : ShortRuns n w s.val := by
  rcases (terminal_iff_runs hn hw s).mp hs with hs | hs
  · exact hs
  · exact False.elim (hlength (exceptionalRuns_cycle_length (by omega) s.property hs))

theorem even_terminal_short {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w) (heven : Even n)
    (s : CycleState n) (hs : ReachabilityQuotient.Terminal (Step n w) s) : ShortRuns n w s.val := by
  rcases (terminal_iff_runs hn hw s).mp hs with hs | hs
  · exact hs
  · exact False.elim (even_cycle_not_exceptional (by omega) s.property heven hs)

theorem classified_returnBy_tendsto_one {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w)
    (P : FiniteMarkov (CycleState n))
    (hsupport : ∀ s t, 0 < P.prob s t → Step n w s t ∨ s = t)
    (hpositive : ∀ s t, Step n w s t → 0 < P.prob s t)
    (s : CycleState n) (hs : ShortRuns n w s.val ∨ ExceptionalRuns n w s.val) :
    Filter.Tendsto (P.returnBy s) Filter.atTop (nhds 1) :=
  terminal_returnBy_tendsto_one P hsupport hpositive s ((terminal_iff_runs hn hw s).mpr hs)

end CycleState
end OddCycle
