import OddCycle.BranchChains
import OddCycle.InterleavedCarry

/-! Explicit head-completion output when the first replacement chooses one
of the two source-to-sink arcs. -/

namespace OddCycle

def arcShift (n source : Nat) (forward : Bool) (len x : Nat) : Nat :=
  let k := cycleCoord n source forward x
  if k < len then cycleLabel n source forward (k - 1) else x

theorem arcShift_label {n source len k : Nat} (hs : source < n) (hk : k < n)
    (forward : Bool) : arcShift n source forward len (cycleLabel n source forward k) =
      if k < len then cycleLabel n source forward (k - 1) else cycleLabel n source forward k := by
  simp only [arcShift, cycleCoord_label hs hk forward]

theorem arc_head_carry {n source len : Nat} (hs : source < n) (hlen : 2 ≤ len)
    (hlt : len < n) (forward : Bool) (b mid : Queue) (extra : Nat)
    (hm : mid ∈ interleavings ((List.range' 2 (len - 2)).map (cycleLabel n source forward)) b)
    (hb : ∀ x ∈ b, ∃ k, len < k ∧ k < n ∧ x = cycleLabel n source forward k) :
    carry (cycleAdjacent n) (len - 1 + extra) source
        (cycleLabel n source forward 1 :: mid ++ [cycleLabel n source forward len]) =
      (source :: mid.map (arcShift n source forward len) ++
        [if extra = 0 then cycleLabel n source forward len else cycleLabel n source forward (len - 1)],
        if extra = 0 then cycleLabel n source forward (len - 1) else cycleLabel n source forward len) := by
  let f := cycleLabel n source forward
  let a := (List.range' 2 (len - 2)).map f
  have hchain : (f 1 :: a).IsChain (fun x y => cycleAdjacent n x y = true ∧
      arcShift n source forward len y = x) := by
    have heq : f 1 :: a = (List.range (len - 1)).map (fun k => f (k + 1)) := by
      have hr : List.range' 1 (len - 1) = 1 :: List.range' 2 (len - 2) := by
        conv_lhs => rw [show len - 1 = (len - 2) + 1 by omega, List.range'_succ]
      rw [← List.map_cons, ← hr]
      simp [List.range'_eq_map_range, f, Nat.add_comm]
    rw [heq, List.isChain_map, List.isChain_range]
    intro k hk
    constructor
    · apply (cycleLabel_adj_iff hs (by omega) (by omega) forward).mpr
      simp [cycleAdjacent, Nat.mod_eq_of_lt (show k + 1 + 1 < n by omega)]
    · rw [arcShift_label hs (by omega) forward, if_pos (by omega)]
      rfl
  have hskip : ∀ x ∈ f 1 :: a, ∀ y ∈ b, cycleAdjacent n x y = false := by
    intro x hx y hy
    obtain ⟨k, hkl, hkn, rfl⟩ := hb y hy
    have hx' : ∃ i, 1 ≤ i ∧ i < len ∧ x = f i := by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨1, by omega, by omega, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        have hi' := List.mem_range'.mp hi
        exact ⟨i, by omega, by omega, rfl⟩
    obtain ⟨i, hil, hiu, rfl⟩ := hx'
    apply Bool.eq_false_iff.mpr
    intro hadj
    have he := (cycleLabel_adj_iff hs (by omega) hkn forward).mp hadj
    rcases (cycleAdjacent_iff (by omega) hkn).mp he with he | he | ⟨he, he'⟩ | ⟨he, he'⟩ <;> omega
  have hfix : ∀ y ∈ b, arcShift n source forward len y = y := by
    intro y hy
    obtain ⟨k, hkl, hkn, rfl⟩ := hb y hy
    rw [arcShift_label hs hkn forward, if_neg (by omega)]
  have hc := carry_interleaved_chain a b mid [f len] (f 1) extra hm hchain hskip hfix
  have hlast : a.getLast?.getD (f 1) = f (len - 1) := by
    simp only [a, List.getLast?_map, List.getLast?_range']
    by_cases he : len - 2 = 0
    · simp only [if_pos he, Option.map_none, Option.getD_none]
      congr 1
      omega
    · simp only [if_neg he, Option.map_some, Option.getD_some]
      congr 1
      omega
  have hadj : cycleAdjacent n (f (len - 1)) (f len) = true := by
    apply (cycleLabel_adj_iff hs (by omega) hlt forward).mpr
    simp [cycleAdjacent, show len - 1 + 1 = len by omega, Nat.mod_eq_of_lt hlt]
  have hstart : cycleAdjacent n source (f 1) = true := by
    rw [← cycleLabel_zero hs forward]
    apply (cycleLabel_adj_iff hs (by omega) (by omega) forward).mpr
    simp [cycleAdjacent, Nat.mod_eq_of_lt (show 1 < n by omega)]
  have hbudget : len - 1 + extra - 1 = a.length + extra := by simp [a]; omega
  simp only [hlast] at hc
  dsimp only [f] at hc hstart hadj
  simp only [List.cons_append, carry, show len - 1 + extra ≠ 0 by omega, if_false,
    hstart, if_true, hbudget, hc]
  by_cases he : extra = 0
  · simp [he]
  · simp [he, hadj]

theorem shortInterior_beyond_long {w source : Nat} (hw : 2 ≤ w) (forward : Bool) :
    ∀ x ∈ shortInterior w source forward, ∃ k, w + 1 < k ∧ k < 2 * w + 1 ∧
      x = cycleLabel (2 * w + 1) source forward k := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  have hj' := List.mem_range.mp hj
  exact ⟨2 * w + 1 - (j + 1), by omega, by omega, rfl⟩

theorem longInterior_beyond_short {w source : Nat} (hw : 2 ≤ w) (forward : Bool) :
    ∀ x ∈ longInterior w source forward, ∃ k, w < k ∧ k < 2 * w + 1 ∧
      x = cycleLabel (2 * w + 1) source (!forward) k := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  have hj' := List.mem_range.mp hj
  refine ⟨2 * w + 1 - (j + 1), by omega, by omega, ?_⟩
  have he := cycleLabel_not (source := source) (show j + 1 < 2 * w + 1 by omega) (!forward)
  simpa only [Bool.not_not, reflect_eq (show j + 1 < 2 * w + 1 by omega),
    if_neg (show j + 1 ≠ 0 by omega)] using he

theorem branch_sink_other {w source : Nat} (hw : 2 ≤ w) (forward : Bool) :
    cycleLabel (2 * w + 1) source (!forward) w = cycleLabel (2 * w + 1) source forward (w + 1) := by
  rw [cycleLabel_not (by omega) forward, reflect_eq (by omega), if_neg (by omega)]
  congr 1
  omega

/-- Exact outputs of every changed head completion in a balanced placement. -/
theorem balanced_changed_head_form {w source bigger : Nat} {q : Queue}
    (hw : 2 ≤ w) (hs : source < 2 * w + 1) (hbig : w < bigger)
    (hv : Valid (2 * w + 1) (q, [])) (forward : Bool)
    (ho : orientation (2 * w + 1) (q, []) = orientation (2 * w + 1) (branchState w source forward))
    (hc : complete (cycleAdjacent (2 * w + 1)) w q 0 ≠
      complete (cycleAdjacent (2 * w + 1)) bigger q 0) :
    ∃ mid, q = source :: cycleLabel (2 * w + 1) source forward 1 :: mid ++
        [cycleLabel (2 * w + 1) source forward (w + 1)] ∧
      mid ∈ interleavings ((List.range' 2 (w - 1)).map (cycleLabel (2 * w + 1) source forward))
        (shortInterior w source forward) ∧
      complete (cycleAdjacent (2 * w + 1)) w q 0 =
        some (source :: mid.map (arcShift (2 * w + 1) source forward (w + 1)) ++
          [cycleLabel (2 * w + 1) source forward (w + 1)],
          cycleLabel (2 * w + 1) source forward w, source) ∧
      complete (cycleAdjacent (2 * w + 1)) bigger q 0 =
        some (source :: mid.map (arcShift (2 * w + 1) source forward (w + 1)) ++
          [cycleLabel (2 * w + 1) source forward w],
          cycleLabel (2 * w + 1) source forward (w + 1), source) := by
  obtain ⟨mid, hm, heq⟩ := placement_interleaving_of_orientation hw hs hv forward ho
  simp only [placement, List.reverse_nil, List.append_nil] at heq
  rcases interleaving_first_branch hw forward hm with ⟨rest, hr, hrest⟩ | ⟨rest, hr, hrest⟩
  · rw [hr] at heq
    refine ⟨rest, heq, hrest, ?_, ?_⟩
    · have he := arc_head_carry (len := w + 1) hs (by omega) (by omega) forward
        (shortInterior w source forward) rest 0 (by simpa using hrest) (shortInterior_beyond_long hw forward)
      simpa [heq, complete] using congrArg (fun r : Queue × Nat => some (r.1, r.2, source)) he
    · have he := arc_head_carry (len := w + 1) hs (by omega) (by omega) forward
        (shortInterior w source forward) rest (bigger - w) (by simpa using hrest) (shortInterior_beyond_long hw forward)
      have hbudget : w + (bigger - w) = bigger := by omega
      simpa [heq, complete, hbudget, show bigger - w ≠ 0 by omega] using
        congrArg (fun r : Queue × Nat => some (r.1, r.2, source)) he
  · have hshort (budget : Nat) (hbudget : w ≤ budget) :
        carry (cycleAdjacent (2 * w + 1)) budget source
          (cycleLabel (2 * w + 1) source (!forward) 1 :: rest ++
            [cycleLabel (2 * w + 1) source forward (w + 1)]) =
          (source :: rest.map (arcShift (2 * w + 1) source (!forward) w) ++
            [cycleLabel (2 * w + 1) source (!forward) (w - 1)],
            cycleLabel (2 * w + 1) source forward (w + 1)) := by
      have he := arc_head_carry hs hw (by omega) (!forward) (longInterior w source forward)
        rest (budget - (w - 1)) hrest (longInterior_beyond_short hw forward)
      have hbudget' : w - 1 + (budget - (w - 1)) = budget := by omega
      simpa only [hbudget', if_neg (show budget - (w - 1) ≠ 0 by omega), branch_sink_other hw forward] using he
    apply False.elim
    apply hc
    rw [heq, hr]
    simp only [List.cons_append] at hshort
    simp only [List.cons_append, complete, hshort w (by omega), hshort bigger (by omega)]

end OddCycle
