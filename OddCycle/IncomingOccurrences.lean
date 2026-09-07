import OddCycle.EventWeights
import OddCycle.Reachability

/-! Incoming events with their queue-position identities retained. -/

namespace OddCycle

structure Occurrence where
  source : State
  side : Bool
  pos : Nat
  initiating : Nat
  deriving DecidableEq

def positions (s : State) : List (Bool × Nat) :=
  (List.range s.1.length).map (false, ·) ++ (List.range s.2.length).map (true, ·)

def selectIncoming (adj : Nat → Nat → Bool) (budget : Nat) (target source : State)
    (position : Bool × Nat) : Option Occurrence := do
  let event ← transition adj budget source position.1 position.2
  if event.1 = target then some ⟨source, position.1, position.2, event.2⟩ else none

def incomingOccurrences (adj : Nat → Nat → Bool) (budget : Nat) (states : List State) (target : State) : List Occurrence :=
  states.flatMap (fun s => (positions s).filterMap (selectIncoming adj budget target s))

theorem selectIncoming_eq_some {adj : Nat → Nat → Bool} {budget : Nat} {target source : State}
    {position : Bool × Nat} {o : Occurrence} :
    selectIncoming adj budget target source position = some o ↔
      o.source = source ∧ (o.side, o.pos) = position ∧
        transition adj budget source position.1 position.2 = some (target, o.initiating) := by
  cases o with
  | mk s side pos initiating =>
    cases position with
    | mk side' pos' =>
      cases he : transition adj budget source side' pos' with
      | none => simp [selectIncoming, he]
      | some e =>
        obtain ⟨t, i⟩ := e
        by_cases ht : t = target
        · subst t
          simp [selectIncoming, he, Occurrence.mk.injEq, Prod.mk.injEq, eq_comm, and_assoc]
        · simp [selectIncoming, he, ht]

theorem mem_positions (s : State) (side : Bool) (pos : Nat) :
    (side, pos) ∈ positions s ↔ pos < (if side then s.2 else s.1).length := by
  cases side <;> simp [positions]

theorem mem_incomingOccurrences {adj : Nat → Nat → Bool} {budget : Nat} {states : List State}
    {target : State} {o : Occurrence} : o ∈ incomingOccurrences adj budget states target ↔
      o.source ∈ states ∧ transition adj budget o.source o.side o.pos = some (target, o.initiating) := by
  simp only [incomingOccurrences, List.mem_flatMap, List.mem_filterMap, selectIncoming_eq_some]
  constructor
  · rintro ⟨s, hs, p, _, heq, hp, ht⟩
    subst s
    subst p
    exact ⟨hs, ht⟩
  · rintro ⟨hs, ht⟩
    exact ⟨o.source, hs, (o.side, o.pos), (mem_positions _ _ _).mpr (transition_pos_lt ht), rfl, rfl, ht⟩

theorem positions_nodup (s : State) : (positions s).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨List.nodup_range.map (fun a b h => (Prod.mk.inj h).2),
    List.nodup_range.map (fun a b h => (Prod.mk.inj h).2), ?_⟩
  intro a ha b hb he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
  have := (Prod.mk.inj he).1
  contradiction

theorem incomingOccurrences_nodup {adj : Nat → Nat → Bool} {budget : Nat} {states : List State}
    (hn : states.Nodup) (target : State) : (incomingOccurrences adj budget states target).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro s _
    apply (positions_nodup s).filterMap
    intro a b o ha hb
    have hsa := (selectIncoming_eq_some.mp ha).2.1
    have hsb := (selectIncoming_eq_some.mp hb).2.1
    exact hsa.symm.trans hsb
  · apply hn.imp
    intro a b hab o ho ho'
    obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp ho
    obtain ⟨p', _, hp'⟩ := List.mem_filterMap.mp ho'
    exact hab ((selectIncoming_eq_some.mp hp).1.symm.trans (selectIncoming_eq_some.mp hp').1)

variable {K : Type*} [Field K]

theorem incomingOccurrences_sum (adj : Nat → Nat → Bool) (budget : Nat) (states : List State)
    (target : State) (rate : Nat → K) (weight : State → K) :
    ((incomingOccurrences adj budget states target).map (fun o => weight o.source * rate o.initiating)).sum =
      (states.map (fun s => incomingRow adj budget rate (weight s) target s)).sum := by
  unfold incomingOccurrences
  rw [List.map_flatMap]
  simp only [List.flatMap_def, List.sum_flatten, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  rw [sum_filterMap, incomingRow_positions]
  have he (position : Bool × Nat) :
      ((selectIncoming adj budget target s position).map (fun o => weight o.source * rate o.initiating)).getD 0 =
        incomingOption rate (weight s) target (transition adj budget s position.1 position.2) := by
    cases ht : transition adj budget s position.1 position.2 with
    | none => simp [selectIncoming, incomingOption, ht]
    | some e =>
      obtain ⟨t, i⟩ := e
      by_cases h : t = target <;> simp [selectIncoming, incomingOption, ht, h]
  simp only [he, positions, List.map_append, List.sum_append, List.map_map, Function.comp_def]

end OddCycle
