import OddCycle.CycleClassification

/-! The positive-position one-swap case of Conjecture 1 on every even cycle.
The class count in the manuscript follows by counting the two alternating
circular Boolean words; the declarations here specialize the general
operational and continuous-time classification and normalized OI law. -/

namespace OddCycle

theorem even_one_swap_terminal_iff {n : Nat} (hn : 4 ≤ n) (heven : Even n)
    (s : CycleState n) :
    ReachabilityQuotient.Terminal (CycleState.Step n 1) s ↔
      ∀ a ∈ cycleRuns n s.val, a = 1 := by
  rw [CycleState.terminal_iff_runs (by omega) (by decide),
    or_iff_left (even_cycle_not_exceptional (by omega) s.property heven)]
  change (∀ a ∈ cycleRuns n s.val, a ≤ 1) ↔ _
  constructor
  · intro h a ha
    have hp := cycleRuns_positive n s.val a ha
    have hl := h a ha
    omega
  · intro h a ha
    rw [h a ha]

theorem PositivePositionAllocation.even_one_swap_recurrent_iff {n : Nat}
    (a : PositivePositionAllocation n) (hn : 4 ≤ n) (heven : Even n) (s : CycleState n) :
    a.pathLaw (by omega) 1 s
      (FiniteMarkov.continuousReturn a.total (a.total_pos (by omega)) s) = 1 ↔
      ∀ r ∈ cycleRuns n s.val, r = 1 := by
  rw [a.continuous_recurrent_iff_runs (by omega) (by decide),
    ← CycleState.terminal_iff_runs (by omega) (by decide),
    even_one_swap_terminal_iff hn heven]

theorem ClosedClass.even_one_swap_normalized_oi {n : Nat} {states : List State}
    (hc : ClosedClass n 1 states) (hn : 4 ≤ n) (heven : Even n)
    (μ ν : PositiveOIAllocation n) :
    let W := normalizedOIWeight μ.toOICapacity ν.toOICapacity states
    OIStationary (cycleAdjacent n) 1 μ.toOICapacity ν.toOICapacity states W ∧
      (states.map W).sum = 1 ∧ ∀ t ∈ states, 0 < W t := by
  have hmod : n % (2 * 1) ≠ 1 := by
    obtain ⟨k, hk⟩ := heven
    omega
  exact hc.safe_normalized_oi (by omega) (by decide) hmod μ ν

end OddCycle
