import OddCycle.GeneralCardinality
import OddCycle.CycleCongruence
import OddCycle.ExceptionalSupport
import OddCycle.GeneralCommunication
import OddCycle.OINormalization

/-! A recurrent-class support is defined directly by the queue event graph. -/

namespace OddCycle

structure ClosedClass (n w : Nat) (states : List State) : Prop where
  nodup : states.Nodup
  nonempty : states ≠ []
  valid : ∀ s ∈ states, Valid n s
  closed : ∀ s ∈ states, ∀ t, EventStep (cycleAdjacent n) w s t → t ∈ states
  communicate : ∀ s ∈ states, ∀ t ∈ states, EventReachable (cycleAdjacent n) w s t

theorem ClosedClass.reachable {n w : Nat} {states : List State} (hc : ClosedClass n w states)
    {s t : State} (hs : s ∈ states) (h : EventReachable (cycleAdjacent n) w s t) : t ∈ states := by
  induction h with
  | refl => exact hs
  | tail _ he ih => exact hc.closed _ ih _ he

theorem ClosedClass.terminal {n w : Nat} {states : List State} (hc : ClosedClass n w states)
    {s : State} (hs : s ∈ states) : ReachabilityQuotient.Terminal (CycleState.Step n w) ⟨s, hc.valid _ hs⟩ := by
  intro t h
  have ht := hc.reachable hs (CycleState.event_reachable_iff.mp h)
  exact CycleState.event_reachable_iff.mpr (hc.communicate _ ht _ hs)

theorem ClosedClass.support {n w : Nat} {states : List State} (hc : ClosedClass n w states) :
    OrientationSupport n states where
  nodup := hc.nodup
  valid := hc.valid
  fiber _ hs _ ht ho := hc.reachable hs (reachable_of_orientation_eq (hc.valid _ hs) ht ho.symm)

theorem ClosedClass.safe_short {n w : Nat} {states : List State} (hc : ClosedClass n w states)
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hmod : n % (2 * w) ≠ 1) : ∀ s ∈ states, height n s ≤ w := by
  intro s hs
  apply (shortRuns_iff_height (by omega) (hc.valid _ hs)).mp
  exact CycleState.terminal_short_of_nonexceptional_length hn hw
    (fun h => hmod ((exceptional_length_iff_mod hn hw).mp h)) ⟨s, hc.valid _ hs⟩ (hc.terminal hs)

theorem ClosedClass.safe_oi_stationary {n w : Nat} {states : List State} (hc : ClosedClass n w states)
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hmod : n % (2 * w) ≠ 1) (μ ν : PositiveOIAllocation n) :
    OIStationary (cycleAdjacent n) w μ.toOICapacity ν.toOICapacity states
      (oiCanonicalWeight μ.toOICapacity ν.toOICapacity) :=
  positive_short_oi_stationary (by omega) hc.support (hc.safe_short hn hw hmod) μ ν

theorem exceptionalStates_closedClass {n w k : Nat} (hw : 1 ≤ w) (hk : 1 ≤ k) (hn : n = 2 * k * w + 1) :
    ClosedClass n w (exceptionalStates n w) where
  nodup := (exceptionalStates_support n w).nodup
  nonempty := by
    obtain ⟨s, hs, he⟩ := exceptionalRuns_exists hw hk hn
    exact List.ne_nil_of_mem (mem_exceptionalStates.mpr ⟨hs, he⟩)
  valid := (exceptionalStates_support n w).valid
  closed s hs t he := by
    obtain ⟨hv, hx⟩ := mem_exceptionalStates.mp hs
    obtain ⟨side, pos, init, he⟩ := he
    exact mem_exceptionalStates.mpr ⟨transition_valid hv he, exceptionalRuns_transition (by nlinarith) hw hv hx he⟩
  communicate s hs t ht := by
    obtain ⟨hv, hx⟩ := mem_exceptionalStates.mp hs
    obtain ⟨hv', hx'⟩ := mem_exceptionalStates.mp ht
    exact exceptionalRuns_communicate (by nlinarith) hw hv hv' hx hx'

theorem balancedStates_closedClass {w : Nat} (hw : 2 ≤ w) : ClosedClass (2 * w + 1) w (balancedStates w) where
  nodup := balancedStates_nodup hw
  nonempty := by
    obtain ⟨s, hv, hb⟩ := balanced_nonempty hw
    exact List.ne_nil_of_mem ((mem_balancedStates_iff hw _).mpr ⟨hv, hb⟩)
  valid s hs := ((mem_balancedStates_iff hw s).mp hs).1
  closed s hs t he := by
    obtain ⟨hv, hb⟩ := (mem_balancedStates_iff hw s).mp hs
    obtain ⟨side, pos, init, he⟩ := he
    exact (mem_balancedStates_iff hw t).mpr ⟨transition_valid hv he, balanced_transition hw hv hb he⟩
  communicate s hs t ht := by
    obtain ⟨hv, hb⟩ := (mem_balancedStates_iff hw s).mp hs
    obtain ⟨hv', hb'⟩ := (mem_balancedStates_iff hw t).mp ht
    exact balanced_communication hw hv hb hv' hb'

end OddCycle
