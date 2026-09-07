import OddCycle.AdditiveOI
import OddCycle.EventWeights

namespace OddCycle

variable {K : Type*} [Field K]

theorem additive_positionRate_event {adj : Nat → Nat → Bool} {budget : Nat} {s t : State}
    {side : Bool} {p init : Nat} (rate : Nat → K)
    (he : transition adj budget s side p = some (t, init)) :
    oiPositionRate (additiveCapacity rate) (additiveCapacity rate) s side p = rate init := by
  have hp := transition_pos_lt he
  have hi := transition_initiating adj budget s side p
  rw [he, Option.map_some, List.getElem?_eq_getElem hp, Option.some.injEq] at hi
  cases side <;> simp only [oiPositionRate, Bool.false_eq_true, if_false, if_true] at hp hi ⊢ <;>
    rw [additive_increment rate _ _ hp] <;> exact congrArg rate hi.symm

theorem oiIncoming_additive (adj : Nat → Nat → Bool) (budget : Nat) (rate : Nat → K)
    (states : List State) (weight : State → K) (target : State) :
    oiIncoming (additiveCapacity rate) (additiveCapacity rate) weight (incomingOccurrences adj budget states target) =
      (states.map (fun s => incomingRow adj budget rate (weight s) target s)).sum := by
  rw [← incomingOccurrences_sum]
  unfold oiIncoming
  apply congrArg List.sum
  apply List.map_congr_left
  intro o ho
  rw [additive_positionRate_event rate (mem_incomingOccurrences.mp ho).2]

theorem balance_incoming_outgoing (adj : Nat → Nat → Bool) (budget : Nat) (rate : Nat → K)
    (states : List State) (hnd : states.Nodup) (weight : State → K) (target : State) (ht : target ∈ states) :
    balance adj budget rate states weight target =
      (states.map (fun s => incomingRow adj budget rate (weight s) target s)).sum -
        weight target * ((target.1 ++ target.2).map rate).sum := by
  have hout (s : State) :
      ((events adj budget s).map (fun e => if s = target then weight s * rate e.2 else 0)).sum =
        if s = target then weight target * ((target.1 ++ target.2).map rate).sum else 0 := by
    by_cases he : s = target
    · subst s
      simp only [if_true, List.sum_map_mul_left]
      have hh := congrArg (fun q : Queue => (q.map rate).sum) (events_initiating adj budget target)
      simpa only [List.map_map, Function.comp_def] using congrArg (weight target * ·) hh
    · simp [he]
  unfold balance
  simp only [sum_map_sub]
  rw [List.map_congr_left (fun s _ => hout s), sum_map_single hnd]
  simp only [ht, if_true, incomingRow]

theorem oiBalance_additive (adj : Nat → Nat → Bool) (budget : Nat) (rate : Nat → K)
    (states : List State) (hnd : states.Nodup) (weight : State → K) (target : State) (ht : target ∈ states) :
    oiBalance adj budget (additiveCapacity rate) (additiveCapacity rate) states weight target =
      balance adj budget rate states weight target := by
  rw [balance_incoming_outgoing adj budget rate states hnd weight target ht]
  unfold oiBalance
  rw [oiIncoming_additive]
  simp only [additiveCapacity, List.map_append, List.sum_append]

end OddCycle
