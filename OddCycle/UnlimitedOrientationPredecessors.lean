import OddCycle.IncomingOccurrences
import OddCycle.UnlimitedPredecessors
import OddCycle.ShortOrientation

/-! Complete unlimited predecessor lists on any union of orientation fibers.
All predecessor membership and uniqueness claims refer to actual transitions. -/

namespace OddCycle

structure OrientationSupport (n : Nat) (states : List State) : Prop where
  nodup : states.Nodup
  valid : ∀ s ∈ states, Valid n s
  fiber : ∀ s ∈ states, ∀ t, Valid n t → orientation n t = orientation n s → t ∈ states

def backwardOccurrence (adj : Nat → Nat → Bool) (rest other : Queue) (d : Nat)
    (side : Bool) (pos : Nat) : Occurrence :=
  ⟨if side then (other, reverseInput adj rest d pos) else (reverseInput adj rest d pos, other),
    side, pos, (unlimitedCarry adj d (rest.drop pos).reverse).2⟩

def sidePredecessors (adj : Nat → Nat → Bool) (rest receiving : Queue) (side : Bool) : List Occurrence :=
  match receiving.reverse with
  | [] => []
  | d :: back => (List.range (rest.length + 1)).map (backwardOccurrence adj rest back.reverse d side)

def unlimitedOccurrences (adj : Nat → Nat → Bool) (target : State) : List Occurrence :=
  sidePredecessors adj target.1 target.2 false ++ sidePredecessors adj target.2 target.1 true

theorem sidePredecessors_nil (adj : Nat → Nat → Bool) (rest : Queue) (side : Bool) :
    sidePredecessors adj rest [] side = [] := rfl

theorem sidePredecessors_concat (adj : Nat → Nat → Bool) (rest other : Queue) (d : Nat) (side : Bool) :
    sidePredecessors adj rest (other ++ [d]) side =
      (List.range (rest.length + 1)).map (backwardOccurrence adj rest other d side) := by
  simp [sidePredecessors]

theorem first_backward_valid {n : Nat} {rest other : Queue} {d : Nat}
    (hv : Valid n (rest, other ++ [d])) (pos : Nat) :
    Valid n (reverseInput (cycleAdjacent n) rest d pos, other) := by
  have hp := (reverseInput_perm (adj := cycleAdjacent n) rest d pos).append_right other
  have hshuffle : ((rest ++ [d]) ++ other).Perm (rest ++ (other ++ [d])) := by
    simpa only [List.append_assoc] using
      (show ([d] ++ other).Perm (other ++ [d]) from List.perm_append_comm).append_left rest
  exact hp.trans (hshuffle.trans hv)

theorem backward_transition {n : Nat} {rest other : Queue} {d pos : Nat} (side : Bool)
    (hv : Valid n (if side then (other ++ [d], rest) else (rest, other ++ [d])))
    (hp : pos ≤ rest.length) :
    transition (cycleAdjacent n) n (backwardOccurrence (cycleAdjacent n) rest other d side pos).source
      side pos = some (if side then (other ++ [d], rest) else (rest, other ++ [d]),
        (backwardOccurrence (cycleAdjacent n) rest other d side pos).initiating) := by
  have hl := hv.length_eq
  have hbudget : rest.length + 1 ≤ n := by cases side <;> simp at hl <;> omega
  have hc := reverseInput_complete (cycleAdjacent_symm n) rest d pos n hp hbudget
  cases side <;> simp [backwardOccurrence, transition, hc]

theorem backward_member {n : Nat} {states : List State} (hs : OrientationSupport n states)
    (hn : 0 < n) {rest other : Queue} {d pos : Nat} (side : Bool)
    (ht : (if side then (other ++ [d], rest) else (rest, other ++ [d])) ∈ states)
    (hp : pos ≤ rest.length) :
    (backwardOccurrence (cycleAdjacent n) rest other d side pos).source ∈ states := by
  have hv := hs.valid _ ht
  have hb : Valid n (backwardOccurrence (cycleAdjacent n) rest other d side pos).source := by
    cases side with
    | false => exact first_backward_valid hv pos
    | true => exact (first_backward_valid hv.exchange pos).exchange
  exact hs.fiber _ ht _ hb
    (large_budget_preserves_orientation hn hb (by omega) (backward_transition side hv hp))

theorem unlimited_first_predecessor {n pos init : Nat} {source : State}
    {rest other : Queue} {d : Nat} (hv : Valid n source)
    (he : transition (cycleAdjacent n) n source false pos = some ((rest, other ++ [d]), init)) :
    source = (reverseInput (cycleAdjacent n) rest d pos, other) ∧ pos ≤ rest.length ∧
      init = (unlimitedCarry (cycleAdjacent n) d (rest.drop pos).reverse).2 := by
  cases hc : complete (cycleAdjacent n) n source.1 pos with
  | none => simp [transition, hc] at he
  | some result =>
    obtain ⟨r, departed, initiating⟩ := result
    simp [transition, hc] at he
    obtain ⟨⟨hr, hh⟩, hi⟩ := he
    subst r
    subst initiating
    obtain ⟨hother, hlast⟩ := hh
    subst departed
    have hlen := hv.length_eq
    simp only [List.length_append, List.length_range] at hlen
    have hr := complete_reverseInput (cycleAdjacent_symm n) (by omega : source.1.length ≤ n) hc
    have hpos := complete_pos_lt hc
    rw [hr.1, reverseInput_length] at hpos
    exact ⟨Prod.ext hr.1 hother, by omega, hr.2⟩

theorem unlimited_first_empty {n pos init : Nat} {source : State} {rest : Queue} :
    transition (cycleAdjacent n) n source false pos ≠ some ((rest, []), init) := by
  intro h
  cases hc : complete (cycleAdjacent n) n source.1 pos with
  | none => simp [transition, hc] at h
  | some result => obtain ⟨r, d, i⟩ := result; simp [transition, hc] at h

theorem mem_sidePredecessors {n : Nat} {states : List State} (hs : OrientationSupport n states)
    (hn : 0 < n) (target : State) (ht : target ∈ states) (o : Occurrence) (side : Bool) :
    o ∈ sidePredecessors (cycleAdjacent n) (if side then target.2 else target.1)
      (if side then target.1 else target.2) side ↔
    o.side = side ∧ o.source ∈ states ∧
      transition (cycleAdjacent n) n o.source side o.pos = some (target, o.initiating) := by
  have first (target : State) (ht : target ∈ states) (o : Occurrence) :
      o ∈ sidePredecessors (cycleAdjacent n) target.1 target.2 false ↔
      o.side = false ∧ o.source ∈ states ∧
        transition (cycleAdjacent n) n o.source false o.pos = some (target, o.initiating) := by
    rcases target with ⟨rest, receiving⟩
    induction receiving using List.reverseRecOn with
    | nil => simp [sidePredecessors, unlimited_first_empty]
    | append_singleton other d _ =>
      dsimp only at ht ⊢
      rw [sidePredecessors_concat]
      constructor
      · intro ho
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
        have hp' : p ≤ rest.length := by have := List.mem_range.mp hp; omega
        exact ⟨rfl, backward_member hs hn false ht hp', backward_transition false (hs.valid _ ht) hp'⟩
      · rintro ⟨hside, hsource, he⟩
        obtain ⟨hq, hp, hi⟩ := unlimited_first_predecessor (hs.valid _ hsource) he
        exact List.mem_map.mpr ⟨o.pos, List.mem_range.mpr (by omega), by
          cases o
          simp_all only [backwardOccurrence, Bool.false_eq_true, if_false, true_and]⟩
  cases side with
  | false => exact first target ht o
  | true =>
    simp only [if_true]
    rcases target with ⟨receiving, rest⟩
    induction receiving using List.reverseRecOn with
    | nil =>
      constructor
      · simp [sidePredecessors]
      · rintro ⟨_, _, he⟩
        exact (unlimited_first_empty (transition_exchange he)).elim
    | append_singleton other d _ =>
      dsimp only at ht ⊢
      rw [sidePredecessors_concat]
      constructor
      · intro ho
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
        have hp' : p ≤ rest.length := by have := List.mem_range.mp hp; omega
        exact ⟨rfl, backward_member hs hn true ht hp', backward_transition true (hs.valid _ ht) hp'⟩
      · rintro ⟨hside, hsource, he⟩
        obtain ⟨hq, hp, hi⟩ := unlimited_first_predecessor (hs.valid _ hsource).exchange (transition_exchange he)
        dsimp only [exchange] at hq hp hi
        have hq' := congrArg exchange hq
        change o.source = (other, reverseInput (cycleAdjacent n) rest d o.pos) at hq'
        exact List.mem_map.mpr ⟨o.pos, List.mem_range.mpr (by omega), by
          cases o
          simp_all only [backwardOccurrence, if_true, true_and]⟩

theorem unlimitedOccurrences_complete {n : Nat} {states : List State} (hs : OrientationSupport n states)
    (hn : 0 < n) (target : State) (ht : target ∈ states) :
    (incomingOccurrences (cycleAdjacent n) n states target).Perm
      (unlimitedOccurrences (cycleAdjacent n) target) := by
  have hnd (rest receiving : Queue) (side : Bool) :
      (sidePredecessors (cycleAdjacent n) rest receiving side).Nodup := by
    unfold sidePredecessors
    split
    · exact List.nodup_nil
    · exact List.nodup_range.map (fun a b h => congrArg Occurrence.pos h)
  have hside {rest receiving : Queue} {side : Bool} {o : Occurrence}
      (ho : o ∈ sidePredecessors (cycleAdjacent n) rest receiving side) : o.side = side := by
    unfold sidePredecessors at ho
    split at ho
    · simp at ho
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp ho; rfl
  have hd : (unlimitedOccurrences (cycleAdjacent n) target).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hnd _ _ _, hnd _ _ _, ?_⟩
    intro a ha b hb he
    have hh := (hside ha).symm.trans (he ▸ hside hb)
    contradiction
  apply (List.perm_ext_iff_of_nodup (incomingOccurrences_nodup hs.nodup target) hd).mpr
  intro o
  rw [mem_incomingOccurrences]
  have hf := mem_sidePredecessors hs hn target ht o false
  have ht' := mem_sidePredecessors hs hn target ht o true
  simp only [Bool.false_eq_true, if_false, if_true] at hf ht'
  simp only [unlimitedOccurrences, List.mem_append, hf, ht']
  cases o.side <;> simp

end OddCycle
