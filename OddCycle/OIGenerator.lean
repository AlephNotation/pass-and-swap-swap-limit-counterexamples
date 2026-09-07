import OddCycle.OIStationary

/-! The OI balance expression is the original position-event generator,
including event multiplicities and diagonal subtraction. -/

namespace OddCycle

variable {K : Type*} [Field K]

def oiPositionIncoming (adj : Nat → Nat → Bool) (budget : Nat) (μ ν : OICapacity K)
    (weight : State → K) (target source : State) (p : Bool × Nat) : K :=
  ((transition adj budget source p.1 p.2).map (fun e =>
    if e.1 = target then weight source * oiPositionRate μ ν source p.1 p.2 else 0)).getD 0

def oiPositionGenerator (adj : Nat → Nat → Bool) (budget : Nat) (μ ν : OICapacity K)
    (states : List State) (weight : State → K) (target : State) : K :=
  (states.map (fun s => ((positions s).map (fun p =>
    oiPositionIncoming adj budget μ ν weight target s p -
      (if s = target then weight s * oiPositionRate μ ν s p.1 p.2 else 0))).sum)).sum

theorem oiIncoming_positions (adj : Nat → Nat → Bool) (budget : Nat) (μ ν : OICapacity K)
    (states : List State) (weight : State → K) (target : State) :
    oiIncoming μ ν weight (incomingOccurrences adj budget states target) =
      (states.map (fun s => ((positions s).map (oiPositionIncoming adj budget μ ν weight target s)).sum)).sum := by
  unfold oiIncoming incomingOccurrences
  rw [List.map_flatMap]
  simp only [List.flatMap_def, List.sum_flatten, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  rw [sum_filterMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  cases he : transition adj budget s p.1 p.2 with
  | none => simp [selectIncoming, oiPositionIncoming, he]
  | some e =>
    obtain ⟨t, i⟩ := e
    by_cases ht : t = target <;> simp [selectIncoming, oiPositionIncoming, he, ht]

theorem oiBalance_eq_positionGenerator (adj : Nat → Nat → Bool) (budget : Nat) (μ ν : OICapacity K)
    (states : List State) (hs : states.Nodup) (weight : State → K) (target : State) (ht : target ∈ states) :
    oiBalance adj budget μ ν states weight target = oiPositionGenerator adj budget μ ν states weight target := by
  have hout (s : State) :
      ((positions s).map (fun p => if s = target then weight s * oiPositionRate μ ν s p.1 p.2 else 0)).sum =
        if s = target then weight target * (μ target.1 + ν target.2) else 0 := by
    by_cases he : s = target
    · subst s
      simp only [if_true, List.sum_map_mul_left, oiPositionRate_sum]
    · simp [he]
  unfold oiPositionGenerator
  simp only [sum_map_sub, hout]
  rw [sum_map_single hs target]
  simp only [ht, if_true]
  rw [oiBalance, oiIncoming_positions]

theorem positions_are_events (adj : Nat → Nat → Bool) (budget : Nat) (s : State)
    {p : Bool × Nat} (hp : p ∈ positions s) : ∃ e, transition adj budget s p.1 p.2 = some e := by
  have hpos := (mem_positions s p.1 p.2).mp hp
  have hi := transition_initiating adj budget s p.1 p.2
  cases he : transition adj budget s p.1 p.2 with
  | none => simp only [he, Option.map_none, List.getElem?_eq_getElem hpos] at hi; contradiction
  | some e => exact ⟨e, rfl⟩

end OddCycle
