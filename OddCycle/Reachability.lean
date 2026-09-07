import OddCycle.PlacementOrder

/-! Reachability in the actual queue-position event graph. When every occupied
position has positive rate, these are exactly the available transitions. -/

namespace OddCycle

def EventStep (adj : Nat → Nat → Bool) (budget : Nat) (s t : State) : Prop :=
  ∃ second pos initiating, transition adj budget s second pos = some (t, initiating)

abbrev EventReachable (adj : Nat → Nat → Bool) (budget : Nat) :=
  Relation.ReflTransGen (EventStep adj budget)

/-- Only completions assigned a strictly positive rate are available. -/
def PositiveEventStep {R : Type*} [Zero R] [LT R] (adj : Nat → Nat → Bool) (budget : Nat)
    (rate : State → Bool → Nat → R) (s t : State) : Prop :=
  ∃ second pos initiating,
    transition adj budget s second pos = some (t, initiating) ∧ 0 < rate s second pos

theorem complete_pos_lt {adj : Nat → Nat → Bool} {budget pos : Nat}
    {q rest : Queue} {departed initiating : Nat}
    (h : complete adj budget q pos = some (rest, departed, initiating)) : pos < q.length := by
  induction q generalizing pos rest departed initiating with
  | nil => simp [complete] at h
  | cons x q ih =>
    cases pos with
    | zero => simp
    | succ pos =>
      cases he : complete adj budget q pos with
      | none => simp [complete, he] at h
      | some result =>
        obtain ⟨r, d, i⟩ := result
        have hh := ih he
        simp only [List.length_cons]
        omega

theorem transition_pos_lt {adj : Nat → Nat → Bool} {budget pos initiating : Nat}
    {s t : State} {second : Bool}
    (h : transition adj budget s second pos = some (t, initiating)) :
    pos < (if second then s.2 else s.1).length := by
  cases he : complete adj budget (if second then s.2 else s.1) pos with
  | none => simp [transition, he] at h
  | some result => exact complete_pos_lt he

theorem EventStep.iff_mem {adj : Nat → Nat → Bool} {budget : Nat} {s t : State} :
    EventStep adj budget s t ↔ ∃ initiating, (t, initiating) ∈ events adj budget s := by
  constructor
  · rintro ⟨second, pos, initiating, h⟩
    refine ⟨initiating, ?_⟩
    have hp := transition_pos_lt h
    cases second
    · exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨pos, List.mem_range.mpr hp, h⟩)
    · exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨pos, List.mem_range.mpr hp, h⟩)
  · rintro ⟨initiating, h⟩
    simp only [events, List.mem_append, List.mem_filterMap] at h
    rcases h with ⟨pos, _, h⟩ | ⟨pos, _, h⟩
    · exact ⟨false, pos, initiating, h⟩
    · exact ⟨true, pos, initiating, h⟩

theorem EventStep.exchange {adj : Nat → Nat → Bool} {budget : Nat} {s t : State}
    (h : EventStep adj budget s t) : EventStep adj budget (exchange s) (exchange t) := by
  obtain ⟨side, pos, job, h⟩ := h
  exact ⟨!side, pos, job, transition_exchange h⟩

theorem EventReachable.exchange {adj : Nat → Nat → Bool} {budget : Nat} {s t : State}
    (h : EventReachable adj budget s t) : EventReachable adj budget (exchange s) (exchange t) :=
  Relation.ReflTransGen.lift OddCycle.exchange (fun _ _ hh => EventStep.exchange hh) h

theorem complete_append {adj : Nat → Nat → Bool} {budget pos : Nat}
    {q rest : Queue} {departed initiating : Nat} (pre : Queue)
    (h : complete adj budget q pos = some (rest, departed, initiating)) :
    complete adj budget (pre ++ q) (pre.length + pos) =
      some (pre ++ rest, departed, initiating) := by
  induction pre with
  | nil => simpa using h
  | cons x pre ih =>
    simp only [List.cons_append, List.length_cons, Nat.succ_add, complete, ih]
    rfl

theorem eventStep_tail (adj : Nat → Nat → Bool) (budget : Nat) (p q : Queue) (x : Nat) :
    EventStep adj budget (p ++ [x], q) (p, q ++ [x]) := by
  refine ⟨false, p.length, x, ?_⟩
  have hc := complete_append p (show complete adj budget [x] 0 = some ([], x, x) by simp [complete, carry])
  simp only [Nat.add_zero, List.append_nil] at hc
  simp [transition, hc]

theorem eventStep_tail_reverse (adj : Nat → Nat → Bool) (budget : Nat) (p q : Queue) (x : Nat) :
    EventStep adj budget (p, q ++ [x]) (p ++ [x], q) :=
  (eventStep_tail adj budget q p x).exchange

/-- Tail completions gather any placement into the first queue and undo this
operation, so every cut of a fixed placement word communicates. -/
theorem gather_reachable (adj : Nat → Nat → Bool) (budget : Nat) (s : State) :
    EventReachable adj budget s (placement s, []) ∧
      EventReachable adj budget (placement s, []) s := by
  obtain ⟨p, q⟩ := s
  induction q using List.reverseRecOn generalizing p with
  | nil => simp only [placement, List.reverse_nil, List.append_nil]; exact ⟨.refl, .refl⟩
  | append_singleton q x ih =>
    have hh := ih (p ++ [x])
    constructor
    · have h := (Relation.ReflTransGen.single (eventStep_tail_reverse adj budget p q x)).trans hh.1
      simpa [placement, List.append_assoc] using h
    · have h := hh.2.trans (Relation.ReflTransGen.single (eventStep_tail adj budget p q x))
      simpa [placement, List.append_assoc] using h

theorem reachable_of_placement_eq {adj : Nat → Nat → Bool} {budget : Nat} {s t : State}
    (h : placement s = placement t) : EventReachable adj budget s t := by
  have hs := (gather_reachable adj budget s).1
  rw [h] at hs
  exact hs.trans (gather_reachable adj budget t).2

/-- An adjacent incompatible pair can be exchanged by completing the first
job with the cut just after the pair. -/
theorem reachable_swap {adj : Nat → Nat → Bool} {budget x y : Nat}
    (hxy : adj x y = false) (p q : Queue) :
    EventReachable adj budget (p ++ x :: y :: q, []) (p ++ y :: x :: q, []) := by
  let s : State := (p ++ [x, y], q.reverse)
  let t : State := (p ++ [y], q.reverse ++ [x])
  have hstep : EventStep adj budget s t := by
    refine ⟨false, p.length, x, ?_⟩
    have hc : complete adj budget [x, y] 0 = some ([y], x, x) := by
      simp [complete, carry, hxy]
    have hh := complete_append p hc
    simp only [Nat.add_zero] at hh
    simp [s, t, transition, hh]
  have hs : placement s = p ++ x :: y :: q := by simp [s, placement, List.append_assoc]
  have ht : placement t = p ++ y :: x :: q := by simp [t, placement, List.append_assoc]
  have h := (gather_reachable adj budget s).2.trans
    ((Relation.ReflTransGen.single hstep).trans (gather_reachable adj budget t).1)
  simpa only [hs, ht] using h

end OddCycle
