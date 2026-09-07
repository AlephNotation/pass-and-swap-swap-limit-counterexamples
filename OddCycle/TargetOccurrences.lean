import OddCycle.TargetPredecessors

/-! A repetition-free list of every incoming unlimited event at the target. -/

namespace OddCycle

def targetOccurrences (w : Nat) : List Occurrence :=
  [⟨firstFlowSource w, false, 0, 0⟩, ⟨firstFlowSource w, false, 1, 2 * w⟩] ++
    (List.range (2 * w + 1)).map (fun pos => ⟨secondFlowSource w pos, true, pos, secondFlowInitiating w pos⟩)

theorem mem_targetOccurrences {w : Nat} (hw : 2 ≤ w) (o : Occurrence) :
    o ∈ targetOccurrences w ↔ o ∈ incomingOccurrences (cycleAdjacent (2 * w + 1)) (2 * w + 1)
      (balancedStates w) (flowTarget w) := by
  rw [mem_incomingOccurrences, mem_balancedStates_iff hw]
  constructor
  · intro ho
    rcases List.mem_append.mp ho with ho | ho
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · exact ⟨firstFlowSource_valid_balanced hw, (firstFlowSource_transitions w).1⟩
      · exact ⟨firstFlowSource_valid_balanced hw, (firstFlowSource_transitions w).2⟩
    · obtain ⟨pos, hp, rfl⟩ := List.mem_map.mp ho
      exact ⟨secondFlowSource_valid_balanced hw,
        secondFlowSource_transition hw (by have := List.mem_range.mp hp; omega)⟩
  · rintro ⟨⟨hv, _⟩, ht⟩
    rcases o with ⟨s, side, pos, initiating⟩
    dsimp only at hv ht
    cases side with
    | false =>
      obtain ⟨hs, hpos⟩ := unlimited_first_incoming hw ht
      rcases hpos with ⟨hp, hi⟩ | ⟨hp, hi⟩ <;> simp [hs, hp, hi, targetOccurrences]
    | true =>
      obtain ⟨hs, hp, hi⟩ := unlimited_second_incoming hv ht
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨pos, List.mem_range.mpr (by omega), by simp only [hs, hi]⟩

theorem targetOccurrences_nodup (w : Nat) : (targetOccurrences w).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨by simp [Occurrence.mk.injEq], ?_, ?_⟩
  · exact List.nodup_range.map (fun a b hab => congrArg Occurrence.pos hab)
  · intro a ha b hb he
    obtain ⟨pos, _, rfl⟩ := List.mem_map.mp hb
    have hs := congrArg Occurrence.side he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> contradiction

theorem targetOccurrences_complete {w : Nat} (hw : 2 ≤ w) :
    (incomingOccurrences (cycleAdjacent (2 * w + 1)) (2 * w + 1) (balancedStates w) (flowTarget w)).Perm
      (targetOccurrences w) := by
  apply (List.perm_ext_iff_of_nodup (incomingOccurrences_nodup (balancedStates_nodup hw) _) (targetOccurrences_nodup w)).mpr
  exact fun o => (mem_targetOccurrences hw o).symm

end OddCycle
