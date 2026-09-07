import OddCycle.OIReverseBalance
import OddCycle.OIPositivity
import OddCycle.UnlimitedOrientationPredecessors

/-! Canonical unlimited balance on unions of orientation fibers. The balance
uses individual queue-position events, with OI prefix-increment rates. -/

namespace OddCycle

variable {K : Type*} [Field K]

def oiCanonicalWeight (μ ν : OICapacity K) (s : State) : K := μ.weight s.1 * ν.weight s.2

def oiPositionRate (μ ν : OICapacity K) (s : State) (side : Bool) (pos : Nat) : K :=
  if side then ν.increment s.2 pos else μ.increment s.1 pos

def oiIncoming (μ ν : OICapacity K) (weight : State → K) (occurrences : List Occurrence) : K :=
  (occurrences.map (fun o => weight o.source * oiPositionRate μ ν o.source o.side o.pos)).sum

/-- The incoming event flow minus the outgoing event flow. Summing the
prefix increments over positions gives the two queues' total capacities. -/
def oiBalance (adj : Nat → Nat → Bool) (budget : Nat) (μ ν : OICapacity K)
    (states : List State) (weight : State → K) (target : State) : K :=
  oiIncoming μ ν weight (incomingOccurrences adj budget states target) -
    weight target * (μ target.1 + ν target.2)

def OIStationary (adj : Nat → Nat → Bool) (budget : Nat) (μ ν : OICapacity K)
    (states : List State) (weight : State → K) : Prop :=
  ∀ target ∈ states, oiBalance adj budget μ ν states weight target = 0

theorem oiPositionRate_sum (μ ν : OICapacity K) (s : State) :
    ((positions s).map (fun p => oiPositionRate μ ν s p.1 p.2)).sum = μ s.1 + ν s.2 := by
  simp only [positions, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    oiPositionRate, Bool.false_eq_true, if_false, if_true, μ.sum_increments, ν.sum_increments]

theorem Valid.first_subperm {n : Nat} {s : State} (hs : Valid n s) : s.1.Subperm (List.range n) :=
  (List.sublist_append_left s.1 s.2).subperm.trans hs.subperm

theorem Valid.second_subperm {n : Nat} {s : State} (hs : Valid n s) : s.2.Subperm (List.range n) :=
  hs.exchange.first_subperm

theorem valid_departing_subperm {n : Nat} {rest other : Queue} {d : Nat}
    (hv : Valid n (rest, other ++ [d])) : (rest ++ [d]).Subperm (List.range n) := by
  have hh := (first_backward_valid hv rest.length).first_subperm
  simpa [reverseInput, unlimitedCarry] using hh

theorem oiIncoming_append (μ ν : OICapacity K) (weight : State → K) (a b : List Occurrence) :
    oiIncoming μ ν weight (a ++ b) = oiIncoming μ ν weight a + oiIncoming μ ν weight b := by
  simp [oiIncoming]

theorem oiIncoming_first (μ ν : OICapacity K) (adj : Nat → Nat → Bool) (rest other : Queue) (d : Nat)
    (hμ : μ.Regular (rest ++ [d])) (hν : ν (other ++ [d]) ≠ 0) :
    oiIncoming μ ν (oiCanonicalWeight μ ν) (sidePredecessors adj rest (other ++ [d]) false) =
      oiCanonicalWeight μ ν (rest, other ++ [d]) * ν (other ++ [d]) := by
  rw [sidePredecessors_concat]
  simp only [oiIncoming, List.map_map, Function.comp_def, backwardOccurrence, oiPositionRate,
    oiCanonicalWeight, Bool.false_eq_true, if_false]
  have hterm (p : Nat) :
      μ.weight (reverseInput adj rest d p) * ν.weight other * μ.increment (reverseInput adj rest d p) p =
      ν.weight other * (μ.weight (reverseInput adj rest d p) * μ.increment (reverseInput adj rest d p) p) := by ring
  simp_rw [hterm]
  rw [List.sum_map_mul_left, μ.unlimited_partial_balance adj rest d hμ, ν.weight_append_singleton]
  field_simp

theorem oiIncoming_second (μ ν : OICapacity K) (adj : Nat → Nat → Bool) (rest other : Queue) (d : Nat)
    (hν : ν.Regular (rest ++ [d])) (hμ : μ (other ++ [d]) ≠ 0) :
    oiIncoming μ ν (oiCanonicalWeight μ ν) (sidePredecessors adj rest (other ++ [d]) true) =
      oiCanonicalWeight μ ν (other ++ [d], rest) * μ (other ++ [d]) := by
  rw [sidePredecessors_concat]
  simp only [oiIncoming, List.map_map, Function.comp_def, backwardOccurrence, oiPositionRate,
    oiCanonicalWeight, if_true, mul_assoc]
  rw [List.sum_map_mul_left, ν.unlimited_partial_balance adj rest d hν, μ.weight_append_singleton]
  field_simp

theorem oiIncoming_side {n : Nat} (μ ν : OICapacity K) (hμ : μ.Regular (List.range n))
    (hν : ν.Regular (List.range n)) (target : State) (ht : Valid n target) (side : Bool) :
    oiIncoming μ ν (oiCanonicalWeight μ ν)
      (sidePredecessors (cycleAdjacent n) (if side then target.2 else target.1)
        (if side then target.1 else target.2) side) =
      oiCanonicalWeight μ ν target * (if side then μ target.1 else ν target.2) := by
  cases side with
  | false =>
    rcases target with ⟨rest, receiving⟩
    induction receiving using List.reverseRecOn with
    | nil => simp [sidePredecessors, oiIncoming, ν.empty]
    | append_singleton other d _ =>
      exact oiIncoming_first μ ν _ rest other d
        (hμ.subperm (valid_departing_subperm ht)) (hν _ ht.second_subperm (by simp))
  | true =>
    rcases target with ⟨receiving, rest⟩
    induction receiving using List.reverseRecOn with
    | nil => simp [sidePredecessors, oiIncoming, μ.empty]
    | append_singleton other d _ =>
      exact oiIncoming_second μ ν _ rest other d
        (hν.subperm (valid_departing_subperm ht.exchange)) (hμ _ ht.first_subperm (by simp))

theorem unlimited_oi_stationary {n : Nat} {states : List State} (hn : 0 < n)
    (hs : OrientationSupport n states) (μ ν : OICapacity K)
    (hμ : μ.Regular (List.range n)) (hν : ν.Regular (List.range n)) :
    OIStationary (cycleAdjacent n) n μ ν states (oiCanonicalWeight μ ν) := by
  intro target ht
  unfold oiBalance
  have hp := unlimitedOccurrences_complete hs hn target ht
  have he := (hp.map (fun o => oiCanonicalWeight μ ν o.source * oiPositionRate μ ν o.source o.side o.pos)).sum_eq
  change oiIncoming μ ν (oiCanonicalWeight μ ν) _ = oiIncoming μ ν (oiCanonicalWeight μ ν) _ at he
  rw [he, unlimitedOccurrences, oiIncoming_append]
  have hf := oiIncoming_side μ ν hμ hν target (hs.valid _ ht) false
  have ht' := oiIncoming_side μ ν hμ hν target (hs.valid _ ht) true
  simp only [Bool.false_eq_true, if_false, if_true] at hf ht'
  rw [hf, ht']
  ring

theorem positive_unlimited_oi_stationary {n : Nat} {states : List State} (hn : 0 < n)
    (hs : OrientationSupport n states) (μ ν : PositiveOIAllocation n) :
    OIStationary (cycleAdjacent n) n μ.toOICapacity ν.toOICapacity states
      (oiCanonicalWeight μ.toOICapacity ν.toOICapacity) :=
  unlimited_oi_stationary hn hs _ _ μ.regular ν.regular

end OddCycle
