import OddCycle.BalancedGeometry
import OddCycle.CycleSymmetry

/-! Exchanging queues reverses every edge. The old sink becomes the new
source, and the long branch runs in the opposite cyclic direction. -/

namespace OddCycle

theorem branchState_reverse_before {w source a b : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (ha : a < 2 * w + 1) (hb : b < 2 * w + 1)
    (hab : cycleAdjacent (2 * w + 1) a b = true) (forward : Bool) :
    (placement (exchange (branchState w source forward))).idxOf a <
        (placement (exchange (branchState w source forward))).idxOf b ↔
      (placement (branchState w (cycleLabel (2 * w + 1) source forward (w + 1))
        (!forward))).idxOf a <
      (placement (branchState w (cycleLabel (2 * w + 1) source forward (w + 1))
        (!forward))).idxOf b := by
  have hn : 0 < 2 * w + 1 := by omega
  have hv := branchState_valid hw hs forward
  rw [placement_exchange,
    idxOf_reverse_lt_iff hv.placement_nodup (hv.placement_mem.mpr ha) (hv.placement_mem.mpr hb)]
  simp only [placement, branchState, List.reverse_nil, List.append_nil]
  rw [branchWord_idxOf hw hs hb forward, branchWord_idxOf hw hs ha forward,
    branchWord_idxOf hw (cycleLabel_lt hn forward) ha (!forward),
    branchWord_idxOf hw (cycleLabel_lt hn forward) hb (!forward),
    cycleCoord_reverse_frame hw hs ha forward, cycleCoord_reverse_frame hw hs hb forward]
  apply foldedIndex_reverse_iff hw (cycleCoord_lt hn forward) (cycleCoord_lt hn forward)
  exact (cycleCoord_adj_iff hs hb ha forward).mpr ((cycleAdjacent_symm _ b a).trans hab)

theorem branchState_reverse_orientation {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (forward : Bool) :
    orientation (2 * w + 1) (exchange (branchState w source forward)) =
      orientation (2 * w + 1)
        (branchState w (cycleLabel (2 * w + 1) source forward (w + 1)) (!forward)) := by
  apply List.map_congr_left
  intro a ha
  have hh := branchState_reverse_before hw hs (List.mem_range.mp ha)
    (Nat.mod_lt (a + 1) (show 0 < 2 * w + 1 by omega))
    (show cycleAdjacent (2 * w + 1) a ((a + 1) % (2 * w + 1)) = true by simp [cycleAdjacent])
    forward
  simp only [hh]

theorem balanced_exchange {w : Nat} (hw : 2 ≤ w) {s : State}
    (hv : Valid (2 * w + 1) s) (hb : balanced w s = true) :
    balanced w (exchange s) = true := by
  simp only [balanced, List.any_eq_true, beq_iff_eq] at hb
  obtain ⟨source, hsource, forward, _, hori⟩ := hb
  have hs := List.mem_range.mp hsource
  change orientation (2 * w + 1) s =
    orientation (2 * w + 1) (branchState w source forward) at hori
  apply balanced_of_orientation_eq
    ((orientation_exchange_eq (by omega) hv (branchState_valid hw hs forward) hori).trans
      (branchState_reverse_orientation hw hs forward))
  exact branchState_balanced (cycleLabel_lt (by omega) forward) (!forward)

end OddCycle
