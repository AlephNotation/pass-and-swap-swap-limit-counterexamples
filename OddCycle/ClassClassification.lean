import OddCycle.ClosedClasses
import OddCycle.GeneralHeight

namespace OddCycle

theorem ClosedClass.short_fiber {n w : Nat} {states : List State} (hc : ClosedClass n w states)
    (hn : 0 < n) {s : State} (hs : s ∈ states) (hw : height n s ≤ w) :
    states.Perm (orientationStates n (orientation n s)) := by
  apply (List.perm_ext_iff_of_nodup hc.nodup (orientationStates_support n _).nodup).mpr
  intro t
  rw [mem_orientationStates]
  constructor
  · intro ht
    exact ⟨hc.valid _ ht, ((short_reachable_iff hn (hc.valid _ hs) (hc.valid _ ht) hw).mp (hc.communicate _ hs _ ht)).symm⟩
  · rintro ⟨ht, ho⟩
    exact hc.reachable hs (reachable_of_orientation_eq (hc.valid _ hs) ht ho.symm)

theorem ClosedClass.exceptional_family {n w : Nat} {states : List State} (hc : ClosedClass n w states)
    (hn : 3 ≤ n) (hw : 1 ≤ w) {s : State} (hs : s ∈ states) (hex : ExceptionalRuns n w s) :
    states.Perm (exceptionalStates n w) := by
  apply (List.perm_ext_iff_of_nodup hc.nodup (exceptionalStates_support n w).nodup).mpr
  intro t
  rw [mem_exceptionalStates]
  constructor
  · intro ht
    exact ⟨hc.valid _ ht, exceptionalRuns_reachable hn hw (hc.valid _ hs) (hc.valid _ ht) hex (hc.communicate _ hs _ ht)⟩
  · rintro ⟨ht, ht'⟩
    exact hc.reachable hs (exceptionalRuns_communicate hn hw (hc.valid _ hs) ht hex ht')

/-- Exhaustive classification of closed communicating classes, stated on
lists of actual queue states rather than on a quotient graph. -/
theorem closed_class_classification {n w : Nat} {states : List State}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hc : ClosedClass n w states) :
    (∃ s ∈ states, height n s ≤ w ∧ states.Perm (orientationStates n (orientation n s))) ∨
      ((∃ k, 1 ≤ k ∧ n = 2 * k * w + 1) ∧ states.Perm (exceptionalStates n w)) := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hc.nonempty
  rcases (CycleState.terminal_iff_runs hn hw ⟨s, hc.valid _ hs⟩).mp (hc.terminal hs) with hs' | hs'
  · have hh := (shortRuns_iff_height (by omega) (hc.valid _ hs)).mp hs'
    exact Or.inl ⟨s, hs, hh, hc.short_fiber (by omega) hs hh⟩
  · exact Or.inr ⟨exceptionalRuns_cycle_length (by omega) (hc.valid _ hs) hs', hc.exceptional_family hn hw hs hs'⟩

theorem balanced_is_exceptional {w : Nat} (hw : 2 ≤ w) :
    (balancedStates w).Perm (exceptionalStates (2 * w + 1) w) := by
  let hc := balancedStates_closedClass hw
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hc.nonempty
  obtain ⟨hv, hb⟩ := (mem_balancedStates_iff hw s).mp hs
  have ht := balanced_height hw hv hb
  have he := (CycleState.terminal_iff_runs (by omega) (by omega) ⟨s, hv⟩).mp (hc.terminal hs)
  apply hc.exceptional_family (by omega) (by omega) hs
  rcases he with he | he
  · have hh := (shortRuns_iff_height (by omega) hv).mp he
    omega
  · exact he

theorem ClosedClass.safe_normalized_oi {n w : Nat} {states : List State} (hc : ClosedClass n w states)
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hmod : n % (2 * w) ≠ 1) (μ ν : PositiveOIAllocation n) :
    let W := normalizedOIWeight μ.toOICapacity ν.toOICapacity states
    OIStationary (cycleAdjacent n) w μ.toOICapacity ν.toOICapacity states W ∧
      (states.map W).sum = 1 ∧ ∀ t ∈ states, 0 < W t :=
  ⟨normalizedOI_stationary (hc.safe_oi_stationary hn hw hmod μ ν),
    normalizedOI_sum (oiNormalizer_pos μ ν hc.valid hc.nonempty).ne',
    fun _ ht => normalizedOI_pos μ ν hc.valid ht⟩

end OddCycle
