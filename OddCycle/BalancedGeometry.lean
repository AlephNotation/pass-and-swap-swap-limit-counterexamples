import OddCycle.CycleGeometry
import OddCycle.PlacementOrder

namespace OddCycle

theorem balanced_of_orientation_eq {w : Nat} {s t : State}
    (h : orientation (2 * w + 1) s = orientation (2 * w + 1) t)
    (hb : balanced w t = true) : balanced w s = true := by
  simpa only [balanced, h] using hb

def branchState (w source : Nat) (forward : Bool) : State :=
  (branchWord w source forward, [])

def frameRank (w source : Nat) (forward : Bool) (x : Nat) : Nat :=
  branchRank w (cycleCoord (2 * w + 1) source forward x)

theorem branchState_valid {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (forward : Bool) : Valid (2 * w + 1) (branchState w source forward) := by
  have hn : 0 < 2 * w + 1 := by omega
  change ((branchWord w source forward) ++ []).Perm _
  rw [List.append_nil, branchWord_eq_map_folded hw hs forward]
  have hnd : ((foldedWord w).map (cycleLabel (2 * w + 1) source forward)).Nodup := by
    apply List.Nodup.map_on _ (foldedWord_nodup w)
    intro a ha b hb hab
    exact cycleLabel_injective hs (foldedWord_mem_iff.mp ha) (foldedWord_mem_iff.mp hb) forward hab
  apply (List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr
  intro x
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, _, rfl⟩
    exact cycleLabel_lt hn forward
  · intro hx
    exact ⟨cycleCoord (2 * w + 1) source forward x,
      foldedWord_mem_iff.mpr (cycleCoord_lt hn forward), cycleLabel_coord hs hx forward⟩

theorem branchState_balanced {w source : Nat} (hs : source < 2 * w + 1) (forward : Bool) :
    balanced w (branchState w source forward) = true := by
  simp only [balanced, List.any_eq_true]
  refine ⟨source, List.mem_range.mpr hs, forward, ?_, ?_⟩
  · cases forward <;> simp
  · simp [branchState]

theorem balanced_nonempty {w : Nat} (hw : 2 ≤ w) :
    ∃ s, Valid (2 * w + 1) s ∧ balanced w s = true :=
  ⟨branchState w 0 true, branchState_valid hw (by omega) true,
    branchState_balanced (by omega) true⟩

theorem branchState_before_rank {w source a b : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (ha : a < 2 * w + 1) (hb : b < 2 * w + 1)
    (hab : cycleAdjacent (2 * w + 1) a b = true) (forward : Bool) :
    (placement (branchState w source forward)).idxOf a <
        (placement (branchState w source forward)).idxOf b ↔
      frameRank w source forward a < frameRank w source forward b := by
  simp only [placement, branchState, List.reverse_nil, List.append_nil]
  rw [branchWord_idxOf hw hs ha forward, branchWord_idxOf hw hs hb forward]
  exact foldedIndex_lt_iff_rank hw (cycleCoord_lt (by omega) forward)
    (cycleCoord_lt (by omega) forward) ((cycleCoord_adj_iff hs ha hb forward).mpr hab)

theorem frameRank_boundary {w source a b : Nat}
    (hs : source < 2 * w + 1) (ha : a < 2 * w + 1) (hb : b < 2 * w + 1)
    (forward : Bool) (hhigh : w ≤ frameRank w source forward a)
    (hup : frameRank w source forward a < frameRank w source forward b) :
    a = cycleLabel (2 * w + 1) source forward w ∧
      b = cycleLabel (2 * w + 1) source forward (w + 1) := by
  obtain ⟨hca, hcb⟩ := branchRank_boundary (cycleCoord_lt (by omega) forward)
    (cycleCoord_lt (by omega) forward) hhigh hup
  constructor
  · exact (cycleCoord_eq_iff hs ha (by omega) forward).mp hca
  · calc
      b = cycleLabel (2 * w + 1) source forward (cycleCoord (2 * w + 1) source forward b) :=
        (cycleLabel_coord hs hb forward).symm
      _ = _ := congrArg (cycleLabel (2 * w + 1) source forward) hcb

theorem rankOrdered_of_orientation {w source : Nat} {s : State}
    (hw : 2 ≤ w) (hs : source < 2 * w + 1) (hv : Valid (2 * w + 1) s)
    (forward : Bool) (hori : orientation (2 * w + 1) s =
      orientation (2 * w + 1) (branchState w source forward)) :
    RankOrdered (cycleAdjacent (2 * w + 1)) (frameRank w source forward) (placement s) := by
  apply rankOrdered_of_before hv.placement_nodup
  intro a ha b hb hab hadj
  have ha' := hv.placement_mem.mp ha
  have hb' := hv.placement_mem.mp hb
  have hbefore := (orientation_before_iff hv (branchState_valid hw hs forward) hori ha' hb' hadj).mp hab
  exact (branchState_before_rank hw hs ha' hb' hadj forward).mp hbefore

theorem branchState_flip_before {w source a b : Nat}
    (hw : 2 ≤ w) (hs : source < 2 * w + 1) (ha : a < 2 * w + 1) (hb : b < 2 * w + 1)
    (hab : cycleAdjacent (2 * w + 1) a b = true) (forward : Bool)
    (hex : ¬ ((a = cycleLabel (2 * w + 1) source forward w ∧
        b = cycleLabel (2 * w + 1) source forward (w + 1)) ∨
      (a = cycleLabel (2 * w + 1) source forward (w + 1) ∧
        b = cycleLabel (2 * w + 1) source forward w))) :
    (placement (branchState w source forward)).idxOf a <
        (placement (branchState w source forward)).idxOf b ↔
      (placement (branchState w source (!forward))).idxOf a <
        (placement (branchState w source (!forward))).idxOf b := by
  simp only [placement, branchState, List.reverse_nil, List.append_nil]
  rw [branchWord_idxOf hw hs ha forward, branchWord_idxOf hw hs hb forward,
    branchWord_idxOf hw hs ha (!forward), branchWord_idxOf hw hs hb (!forward),
    cycleCoord_not (by omega) forward, cycleCoord_not (by omega) forward]
  apply foldedIndex_flip_iff hw (cycleCoord_lt (by omega) forward)
    (cycleCoord_lt (by omega) forward) ((cycleCoord_adj_iff hs ha hb forward).mpr hab)
  intro h
  apply hex
  rcases h with ⟨hca, hcb⟩ | ⟨hca, hcb⟩
  · exact Or.inl ⟨(cycleCoord_eq_iff hs ha (by omega) forward).mp hca,
      (cycleCoord_eq_iff hs hb (by omega) forward).mp hcb⟩
  · exact Or.inr ⟨(cycleCoord_eq_iff hs ha (by omega) forward).mp hca,
      (cycleCoord_eq_iff hs hb (by omega) forward).mp hcb⟩

theorem branchState_boundary_before {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (forward : Bool) :
    (placement (branchState w source forward)).idxOf (cycleLabel (2 * w + 1) source forward w) <
      (placement (branchState w source forward)).idxOf (cycleLabel (2 * w + 1) source forward (w + 1)) := by
  simp only [placement, branchState, List.reverse_nil, List.append_nil]
  rw [branchWord_idxOf_label hw hs (by omega) forward, branchWord_idxOf_label hw hs (by omega) forward]
  unfold foldedIndex
  split_ifs <;> omega

theorem branchState_flip_boundary_before {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (forward : Bool) :
    (placement (branchState w source (!forward))).idxOf (cycleLabel (2 * w + 1) source forward (w + 1)) <
      (placement (branchState w source (!forward))).idxOf (cycleLabel (2 * w + 1) source forward w) := by
  have hn : 0 < 2 * w + 1 := by omega
  simp only [placement, branchState, List.reverse_nil, List.append_nil]
  rw [branchWord_idxOf hw hs (cycleLabel_lt hn forward) (!forward),
    branchWord_idxOf hw hs (cycleLabel_lt hn forward) (!forward)]
  rw [cycleCoord_not hn forward, cycleCoord_not hn forward,
    cycleCoord_label hs (by omega) forward, cycleCoord_label hs (by omega) forward,
    reflect_eq (show w + 1 < 2 * w + 1 by omega), reflect_eq (show w < 2 * w + 1 by omega)]
  unfold foldedIndex
  split_ifs <;> omega

end OddCycle
