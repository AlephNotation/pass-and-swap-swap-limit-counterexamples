import OddCycle.ChangedReconstruction
import OddCycle.BalancedWords

/-! The two source words and their exchanged destinations, uniformly in w.
The coordinate descriptions are linked to the paper's explicit label words. -/

namespace OddCycle

def flowCore (w : Nat) : Queue := shortInterior w w true ++ shortInterior w w false
def flowQueue (w : Nat) : Queue := w :: flowCore w ++ [2 * w]
def flowWordX (w : Nat) : Queue := branchWord w w false
def flowWordY (w : Nat) : Queue :=
  w :: cycleLabel (2 * w + 1) w true 1 ::
    (shortInterior w w true ++ (List.range' 2 (w - 1)).map (cycleLabel (2 * w + 1) w true)) ++ [0]

def flowTarget (w : Nat) : State := ([0], flowQueue w)
def flowSourceX (w : Nat) : State := ([], flowWordX w)
def flowSourceY (w : Nat) : State := ([], flowWordY w)

theorem flow_endpoints {w : Nat} (hw : 2 ≤ w) :
    cycleLabel (2 * w + 1) w false w = 0 ∧
    cycleLabel (2 * w + 1) w false (w + 1) = 2 * w ∧
    cycleLabel (2 * w + 1) w true w = 2 * w ∧
    cycleLabel (2 * w + 1) w true (w + 1) = 0 := by
  have h1 : w + (2 * w + 1 - w) = 2 * w + 1 := by omega
  have h2 : w + (2 * w - w) = 2 * w := by omega
  simp [cycleLabel, h1, h2, show w + w = 2 * w by omega,
    show w + (w + 1) = 2 * w + 1 by omega, Nat.mod_eq_of_lt (show 2 * w < 2 * w + 1 by omega)]

theorem shifted_long_tail {w source : Nat} (hw : 2 ≤ w) (hs : source < 2 * w + 1) (forward : Bool) :
    ((List.range' 2 (w - 1)).map (cycleLabel (2 * w + 1) source forward)).map
      (arcShift (2 * w + 1) source forward (w + 1)) = shortInterior w source (!forward) := by
  rw [shortInterior_eq_range' hw, Bool.not_not]
  simp only [List.range'_eq_map_range, List.map_map]
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp hj
  simp only [Function.comp_apply]
  rw [arcShift_label hs (by omega) forward, if_pos (by omega)]
  congr 1
  omega

theorem shifted_short_interior {w source : Nat} (hw : 2 ≤ w) (hs : source < 2 * w + 1) (forward : Bool) :
    (shortInterior w source forward).map (arcShift (2 * w + 1) source forward (w + 1)) =
      shortInterior w source forward := by
  calc
    _ = (shortInterior w source forward).map id := by
      apply List.map_congr_left
      intro x hx
      obtain ⟨k, hkl, hkn, rfl⟩ := shortInterior_beyond_long hw forward x hx
      rw [arcShift_label hs hkn forward, if_neg (by omega)]
      rfl
    _ = _ := List.map_id _

theorem append_mem_interleavings (a b : Queue) : a ++ b ∈ interleavings a b := by
  induction a generalizing b with
  | nil => simp [interleavings]
  | cons x xs ih =>
    cases b with
    | nil => simp [interleavings]
    | cons y ys =>
      rw [interleavings, List.mem_append]
      exact Or.inl (List.mem_map.mpr ⟨xs ++ y :: ys, ih _, rfl⟩)

theorem flowX_complete {w bigger : Nat} (hw : 2 ≤ w) (hbig : w < bigger) :
    complete (cycleAdjacent (2 * w + 1)) w (flowWordX w) 0 = some (flowQueue w, 0, w) ∧
    complete (cycleAdjacent (2 * w + 1)) bigger (flowWordX w) 0 =
      some (w :: flowCore w ++ [0], 2 * w, w) := by
  have hs : w < 2 * w + 1 := by omega
  let a := (List.range' 2 (w - 1)).map (cycleLabel (2 * w + 1) w false)
  let b := shortInterior w w false
  have hword : flowWordX w = w :: cycleLabel (2 * w + 1) w false 1 :: (a ++ b) ++ [2 * w] := by
    rw [flowWordX, branchWord_eq_interiors, (flow_endpoints hw).2.1, longInterior_eq_range']
    have he : List.range' 1 w = 1 :: List.range' 2 (w - 1) := by
      conv_lhs => rw [show w = (w - 1) + 1 by omega, List.range'_succ]
    rw [he, List.map_cons]
    rfl
  have he (extra : Nat) := arc_head_carry (len := w + 1) hs (by omega) (by omega) false
    b (a ++ b) extra (by simpa only [Nat.add_sub_cancel] using append_mem_interleavings a b)
    (shortInterior_beyond_long hw false)
  have hmap : (a ++ b).map (arcShift (2 * w + 1) w false (w + 1)) = flowCore w := by
    rw [List.map_append, shifted_long_tail hw hs false, shifted_short_interior hw hs false]
    rfl
  constructor
  · have hh := he 0
    simpa [hword, complete, hmap, (flow_endpoints hw).1, (flow_endpoints hw).2.1, flowQueue] using
      congrArg (fun r : Queue × Nat => some (r.1, r.2, w)) hh
  · have hh := he (bigger - w)
    have hbudget : w + (bigger - w) = bigger := by omega
    simpa [hword, complete, hmap, (flow_endpoints hw).1, (flow_endpoints hw).2.1,
      hbudget, show bigger - w ≠ 0 by omega] using congrArg (fun r : Queue × Nat => some (r.1, r.2, w)) hh

theorem flowY_complete {w bigger : Nat} (hw : 2 ≤ w) (hbig : w < bigger) :
    complete (cycleAdjacent (2 * w + 1)) w (flowWordY w) 0 =
      some (w :: flowCore w ++ [0], 2 * w, w) ∧
    complete (cycleAdjacent (2 * w + 1)) bigger (flowWordY w) 0 = some (flowQueue w, 0, w) := by
  have hs : w < 2 * w + 1 := by omega
  let a := (List.range' 2 (w - 1)).map (cycleLabel (2 * w + 1) w true)
  let b := shortInterior w w true
  have he (extra : Nat) := arc_head_carry (len := w + 1) hs (by omega) (by omega) true
    b (b ++ a) extra (by simpa only [Nat.add_sub_cancel] using
      (interleavings_swap b a).mem_iff.mp (append_mem_interleavings b a))
    (shortInterior_beyond_long hw true)
  have hmap : (b ++ a).map (arcShift (2 * w + 1) w true (w + 1)) = flowCore w := by
    rw [List.map_append, shifted_short_interior hw hs true, shifted_long_tail hw hs true]
    rfl
  constructor
  · have hh := he 0
    simpa [flowWordY, complete, hmap, (flow_endpoints hw).2.2.1, (flow_endpoints hw).2.2.2, a, b] using
      congrArg (fun r : Queue × Nat => some (r.1, r.2, w)) hh
  · have hh := he (bigger - w)
    have hbudget : w + (bigger - w) = bigger := by omega
    simpa [flowWordY, complete, hmap, (flow_endpoints hw).2.2.1, (flow_endpoints hw).2.2.2,
      hbudget, show bigger - w ≠ 0 by omega, flowQueue, a, b] using
      congrArg (fun r : Queue × Nat => some (r.1, r.2, w)) hh

theorem flowY_frame {w : Nat} (hw : 2 ≤ w) :
    Valid (2 * w + 1) (flowWordY w, []) ∧
      orientation (2 * w + 1) (flowWordY w, []) = orientation (2 * w + 1) (branchState w w true) := by
  have hs : w < 2 * w + 1 := by omega
  let f := cycleLabel (2 * w + 1) w true
  let a := (List.range' 2 (w - 1)).map f
  let b := shortInterior w w true
  have hl : longInterior w w true = f 1 :: a := by
    rw [longInterior_eq_range']
    have he : List.range' 1 w = 1 :: List.range' 2 (w - 1) := by
      conv_lhs => rw [show w = (w - 1) + 1 by omega, List.range'_succ]
    rw [he, List.map_cons]
  have hm : f 1 :: (b ++ a) ∈ interleavings (longInterior w w true) b := by
    apply (mem_interleavings_iff (interiors_nodup hw hs true)).mpr
    rw [hl]
    refine ⟨?_, ?_, ?_⟩
    · exact List.perm_append_comm.cons (f 1)
    · exact (List.sublist_append_right b a).cons₂ (f 1)
    · exact (List.sublist_append_left b a).cons (f 1)
  apply (mem_frameWords_iff hw hs true _).mp
  apply List.mem_map.mpr
  refine ⟨f 1 :: (b ++ a), hm, ?_⟩
  simp [flowWordY, (flow_endpoints hw).2.2.2, f, a, b]

theorem flowX_changed {w bigger : Nat} (hw : 2 ≤ w) (hbig : w < bigger) :
    complete (cycleAdjacent (2 * w + 1)) w (flowWordX w) 0 ≠
      complete (cycleAdjacent (2 * w + 1)) bigger (flowWordX w) 0 := by
  rw [(flowX_complete hw hbig).1, (flowX_complete hw hbig).2]
  intro he
  have hh := congrArg (Option.map (fun r : Queue × Nat × Nat => r.2.1)) he
  simp only [Option.map_some, Option.some.injEq] at hh
  omega

theorem flowY_changed {w bigger : Nat} (hw : 2 ≤ w) (hbig : w < bigger) :
    complete (cycleAdjacent (2 * w + 1)) w (flowWordY w) 0 ≠
      complete (cycleAdjacent (2 * w + 1)) bigger (flowWordY w) 0 := by
  rw [(flowY_complete hw hbig).1, (flowY_complete hw hbig).2]
  intro he
  have hh := congrArg (Option.map (fun r : Queue × Nat × Nat => r.2.1)) he
  simp only [Option.map_some, Option.some.injEq] at hh
  omega

end OddCycle
