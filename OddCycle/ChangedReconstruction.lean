import OddCycle.ArcCarry
import OddCycle.ChangedEvents

/-! Inverting the retained labels reconstructs a changed head completion
uniquely once its balanced frame is fixed. -/

namespace OddCycle

def arcUnshift (n source : Nat) (forward : Bool) (len x : Nat) : Nat :=
  let k := cycleCoord n source forward x
  if k < len - 1 then cycleLabel n source forward (k + 1) else x

theorem arcUnshift_shift {n source len x : Nat} (hs : source < n)
    (hx : x < n) (hxs : x ≠ source) (forward : Bool) :
    arcUnshift n source forward len (arcShift n source forward len x) = x := by
  have hk := cycleCoord_lt (show 0 < n by omega) forward (source := source) (k := x)
  have hk0 : cycleCoord n source forward x ≠ 0 := by
    intro h
    have he := (cycleCoord_eq_iff hs hx (by omega) forward).mp h
    exact hxs (by simpa only [cycleLabel_zero hs forward] using he)
  unfold arcShift
  dsimp only
  split_ifs with hlt
  · simp only [arcUnshift, cycleCoord_label hs (show cycleCoord n source forward x - 1 < n by omega) forward,
      if_pos (show cycleCoord n source forward x - 1 < len - 1 by omega)]
    rw [show cycleCoord n source forward x - 1 + 1 = cycleCoord n source forward x by omega,
      cycleLabel_coord hs hx forward]
  · simp only [arcUnshift, if_neg (show ¬cycleCoord n source forward x < len - 1 by omega)]

theorem arcShift_map_injective {n source len : Nat} (hs : source < n)
    (forward : Bool) {a b : Queue}
    (ha : ∀ x ∈ a, x < n ∧ x ≠ source) (hb : ∀ x ∈ b, x < n ∧ x ≠ source)
    (he : a.map (arcShift n source forward len) = b.map (arcShift n source forward len)) : a = b := by
  have hmap (q : Queue) (hq : ∀ x ∈ q, x < n ∧ x ≠ source) :
      (q.map (arcShift n source forward len)).map (arcUnshift n source forward len) = q := by
    rw [List.map_map]
    calc
      _ = q.map id := List.map_congr_left (fun x hx => arcUnshift_shift hs (hq x hx).1 (hq x hx).2 forward)
      _ = q := List.map_id q
  have := congrArg (List.map (arcUnshift n source forward len)) he
  simpa only [hmap a ha, hmap b hb] using this

theorem changed_mid_labels {n source first last : Nat} {q mid : Queue}
    (hv : Valid n (q, [])) (hq : q = source :: first :: mid ++ [last]) :
    ∀ x ∈ mid, x < n ∧ x ≠ source := by
  intro x hx
  have hm : x ∈ placement (q, []) := by simp [placement, hq, hx]
  refine ⟨hv.placement_mem.mp hm, ?_⟩
  intro he
  subst x
  have hn := hv.placement_nodup
  simp only [placement, List.reverse_nil, List.append_nil, hq, List.cons_append] at hn
  exact (List.nodup_cons.mp hn).1 (by simp [hx])

/-- Both the limited and the unlimited output determine the changed input word. -/
theorem balanced_changed_head_injective {w source bigger : Nat} {q r : Queue}
    (hw : 2 ≤ w) (hs : source < 2 * w + 1) (hbig : w < bigger) (forward : Bool)
    (hq : Valid (2 * w + 1) (q, [])) (hr : Valid (2 * w + 1) (r, []))
    (hoq : orientation (2 * w + 1) (q, []) = orientation (2 * w + 1) (branchState w source forward))
    (hor : orientation (2 * w + 1) (r, []) = orientation (2 * w + 1) (branchState w source forward))
    (hcq : complete (cycleAdjacent (2 * w + 1)) w q 0 ≠ complete (cycleAdjacent (2 * w + 1)) bigger q 0)
    (hcr : complete (cycleAdjacent (2 * w + 1)) w r 0 ≠ complete (cycleAdjacent (2 * w + 1)) bigger r 0)
    (he : complete (cycleAdjacent (2 * w + 1)) w q 0 = complete (cycleAdjacent (2 * w + 1)) w r 0 ∨
      complete (cycleAdjacent (2 * w + 1)) bigger q 0 = complete (cycleAdjacent (2 * w + 1)) bigger r 0) : q = r := by
  obtain ⟨a, hqa, _, hqaL, hqaU⟩ := balanced_changed_head_form hw hs hbig hq forward hoq hcq
  obtain ⟨b, hrb, _, hrbL, hrbU⟩ := balanced_changed_head_form hw hs hbig hr forward hor hcr
  have hmap : a.map (arcShift (2 * w + 1) source forward (w + 1)) =
      b.map (arcShift (2 * w + 1) source forward (w + 1)) := by
    rcases he with he | he
    · simpa only [hqaL, hrbL, Option.some.injEq, Prod.mk.injEq, List.append_cancel_right_eq,
        List.cons.injEq, true_and, and_true] using he
    · simpa only [hqaU, hrbU, Option.some.injEq, Prod.mk.injEq, List.append_cancel_right_eq,
        List.cons.injEq, true_and, and_true] using he
  have hab := arcShift_map_injective hs forward
    (changed_mid_labels hq hqa) (changed_mid_labels hr hrb) hmap
  simp only [hqa, hrb, hab]

end OddCycle
