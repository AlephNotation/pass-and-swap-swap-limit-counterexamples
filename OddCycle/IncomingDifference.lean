import OddCycle.OIGenerator

/-! Cancelling unchanged events leaves the gained and lost predecessors,
with occurrence identities and multiplicities retained. -/

namespace OddCycle

def gainedOccurrences (adj : Nat → Nat → Bool) (small big : Nat) (states : List State) (target : State) : List Occurrence :=
  (incomingOccurrences adj small states target).filter
    (fun o => !(incomingOccurrences adj big states target).contains o)

theorem mem_gainedOccurrences {adj : Nat → Nat → Bool} {small big : Nat} {states : List State}
    {target : State} {o : Occurrence} : o ∈ gainedOccurrences adj small big states target ↔
    o.source ∈ states ∧ transition adj small o.source o.side o.pos = some (target, o.initiating) ∧
      transition adj big o.source o.side o.pos ≠ some (target, o.initiating) := by
  simp [gainedOccurrences, mem_incomingOccurrences]
  tauto

theorem gainedOccurrences_nodup {adj : Nat → Nat → Bool} {small big : Nat} {states : List State}
    (hs : states.Nodup) (target : State) : (gainedOccurrences adj small big states target).Nodup :=
  (incomingOccurrences_nodup hs target).filter _

variable {K : Type*} [Field K]

theorem list_weight_partition {α : Type*} (q : List α) (p : α → Bool) (weight : α → K) :
    (q.map weight).sum = ((q.filter p).map weight).sum + ((q.filter (fun x => !(p x))).map weight).sum := by
  induction q with
  | nil => simp
  | cons x xs ih => cases hx : p x <;> simp [hx, ih] <;> ring

theorem list_weight_difference {α : Type*} [DecidableEq α] (a b : List α)
    (ha : a.Nodup) (hb : b.Nodup) (weight : α → K) :
    (a.map weight).sum - (b.map weight).sum =
      ((a.filter (fun x => !b.contains x)).map weight).sum -
        ((b.filter (fun x => !a.contains x)).map weight).sum := by
  have hp : (a.filter b.contains).Perm (b.filter a.contains) := by
    apply (List.perm_ext_iff_of_nodup (ha.filter _) (hb.filter _)).mpr
    intro x
    simp [and_comm]
  have he := (hp.map weight).sum_eq
  have hpa := list_weight_partition a b.contains weight
  have hpb := list_weight_partition b a.contains weight
  rw [hpa, hpb, he]
  ring

theorem oiBalance_difference_gained (adj : Nat → Nat → Bool) (small big : Nat) (μ ν : OICapacity K)
    (states : List State) (hs : states.Nodup) (weight : State → K) (target : State) :
    oiBalance adj small μ ν states weight target - oiBalance adj big μ ν states weight target =
      oiIncoming μ ν weight (gainedOccurrences adj small big states target) -
        oiIncoming μ ν weight (gainedOccurrences adj big small states target) := by
  unfold oiBalance oiIncoming gainedOccurrences
  have h := list_weight_difference (incomingOccurrences adj small states target)
    (incomingOccurrences adj big states target) (incomingOccurrences_nodup hs target)
    (incomingOccurrences_nodup hs target) (fun o => weight o.source * oiPositionRate μ ν o.source o.side o.pos)
  rw [show ∀ a b c : K, (a - c) - (b - c) = a - b by intros; ring]
  exact h

end OddCycle
