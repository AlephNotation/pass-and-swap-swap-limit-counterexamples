import OddCycle.WordCommunication

/-!
Reachability quotients with communicating fibers. These are quotients of
directed graphs, not lumped stochastic processes: no condition on the rates
of transitions between fibers is needed or asserted.
-/

namespace OddCycle

namespace ReachabilityQuotient

variable {S O : Type*} (step : S → S → Prop) (project : S → O)

abbrev Reach := Relation.ReflTransGen step

/-- Membership in a terminal strongly connected component. -/
def Terminal (x : S) : Prop := ∀ y, Reach step x y → Reach step y x

/-- An edge exists when some representatives admit an operational edge. -/
def Step (a b : O) : Prop :=
  ∃ x y, project x = a ∧ project y = b ∧ step x y

theorem project_reach {x y : S} (h : Reach step x y) :
    Reach (Step step project) (project x) (project y) :=
  Relation.ReflTransGen.lift project (fun a b hab => ⟨a, b, rfl, rfl, hab⟩) h

variable (fiber : ∀ x y, project x = project y → Reach step x y)
include fiber

/-- A quotient walk lifts from any representative of its initial fiber. -/
theorem lift_reach {x : S} {b : O}
    (h : Reach (Step step project) (project x) b) :
    ∃ y, project y = b ∧ Reach step x y := by
  induction h with
  | refl => exact ⟨x, rfl, .refl⟩
  | @tail a b _ hab ih =>
    obtain ⟨y, hy, hxy⟩ := ih
    obtain ⟨u, v, hu, hv, huv⟩ := hab
    exact ⟨v, hv, hxy.trans ((fiber y u (hy.trans hu.symm)).tail huv)⟩

theorem reach_iff {x y : S} :
    Reach step x y ↔ Reach (Step step project) (project x) (project y) := by
  constructor
  · exact project_reach step project
  · intro h
    obtain ⟨z, hz, hxz⟩ := lift_reach step project fiber h
    exact hxz.trans (fiber z y hz)

/-- Terminal components correspond, without finiteness or lumpability. -/
theorem terminal_iff (x : S) :
    Terminal step x ↔ Terminal (Step step project) (project x) := by
  constructor
  · intro hx b hb
    obtain ⟨y, hy, hxy⟩ := lift_reach step project fiber hb
    simpa only [hy] using project_reach step project (hx y hxy)
  · intro hx y hxy
    exact (reach_iff step project fiber).mpr
      (hx (project y) (project_reach step project hxy))

end ReachabilityQuotient

/-- Actual fixed-population queue configurations, without enumerating them. -/
abbrev CycleState (n : Nat) := {s : State // Valid n s}

namespace CycleState

def Step (n w : Nat) (s t : CycleState n) : Prop :=
  EventStep (cycleAdjacent n) w s.val t.val

def project (n : Nat) (s : CycleState n) : List Bool := orientation n s.val

theorem lift_event_reachable {n w : Nat} {s : CycleState n} {t : State}
    (h : EventReachable (cycleAdjacent n) w s.val t) :
    ∃ ht : Valid n t,
      Relation.ReflTransGen (Step n w) s ⟨t, ht⟩ := by
  induction h with
  | refl => exact ⟨s.property, .refl⟩
  | @tail a b _ hab ih =>
    obtain ⟨ha, hsa⟩ := ih
    obtain ⟨side, pos, job, he⟩ := hab
    have hb := transition_valid ha he
    exact ⟨hb, hsa.tail ⟨side, pos, job, he⟩⟩

theorem event_reachable_iff {n w : Nat} {s t : CycleState n} :
    Relation.ReflTransGen (Step n w) s t ↔
      EventReachable (cycleAdjacent n) w s.val t.val := by
  constructor
  · exact Relation.ReflTransGen.lift Subtype.val (fun _ _ h => h)
  · intro h
    obtain ⟨ht, hp⟩ := lift_event_reachable h
    exact hp

theorem fiber {n w : Nat} (s t : CycleState n) (h : project n s = project n t) :
    Relation.ReflTransGen (Step n w) s t :=
  event_reachable_iff.mpr (reachable_of_orientation_eq s.property t.property h)

/-- The exact existence-of-an-operational-edge quotient. Its identification
with a local binary-word rule is a separate mathematical obligation. -/
abbrev OrientationStep (n w : Nat) :=
  ReachabilityQuotient.Step (Step n w) (project n)

theorem orientation_reachable_iff {n w : Nat} {s t : CycleState n} :
    EventReachable (cycleAdjacent n) w s.val t.val ↔
      Relation.ReflTransGen (OrientationStep n w) (project n s) (project n t) := by
  rw [← event_reachable_iff]
  exact ReachabilityQuotient.reach_iff (Step n w) (project n) fiber

theorem terminal_orientation_iff {n w : Nat} (s : CycleState n) :
    ReachabilityQuotient.Terminal (Step n w) s ↔
      ReachabilityQuotient.Terminal (OrientationStep n w) (project n s) :=
  ReachabilityQuotient.terminal_iff (Step n w) (project n) fiber s

end CycleState
end OddCycle
