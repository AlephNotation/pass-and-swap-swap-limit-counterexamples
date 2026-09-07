import OddCycle.BranchChains
import OddCycle.BudgetStability

/-! A changed balanced event must complete the head of the queue containing
the entire population. The larger comparison budget can be arbitrary. -/

namespace OddCycle

theorem frameRank_zero_iff {w source x : Nat} (hs : source < 2 * w + 1)
    (hx : x < 2 * w + 1) (forward : Bool) : frameRank w source forward x = 0 ↔ x = source := by
  have hc := cycleCoord_lt (show 0 < 2 * w + 1 by omega) forward (source := source) (k := x)
  have hr : branchRank w (cycleCoord (2 * w + 1) source forward x) = 0 ↔
      cycleCoord (2 * w + 1) source forward x = 0 := by
    unfold branchRank
    split_ifs <;> omega
  rw [frameRank, hr, cycleCoord_eq_iff hs hx (by omega) forward, cycleLabel_zero hs forward]

theorem frameRank_top_iff {w source x : Nat} (hw : 0 < w) (hs : source < 2 * w + 1)
    (hx : x < 2 * w + 1) (forward : Bool) : frameRank w source forward x = w + 1 ↔
      x = cycleLabel (2 * w + 1) source forward (w + 1) := by
  have hc := cycleCoord_lt (show 0 < 2 * w + 1 by omega) forward (source := source) (k := x)
  have hr : branchRank w (cycleCoord (2 * w + 1) source forward x) = w + 1 ↔
      cycleCoord (2 * w + 1) source forward x = w + 1 := by
    unfold branchRank
    split_ifs <;> omega
  rw [frameRank, hr, cycleCoord_eq_iff hs hx (by omega) forward]

theorem balanced_first_budget_stable {w bigger : Nat} {s : State} (hw : 2 ≤ w)
    (hbig : w ≤ bigger) (hv : Valid (2 * w + 1) s) (hb : balanced w s = true) (pos : Nat)
    (hproper : s.2 ≠ [] ∨ pos ≠ 0) :
    transition (cycleAdjacent (2 * w + 1)) w s false pos =
      transition (cycleAdjacent (2 * w + 1)) bigger s false pos := by
  simp only [balanced, List.any_eq_true, beq_iff_eq] at hb
  obtain ⟨source, hsource, forward, _, hori⟩ := hb
  have hs := List.mem_range.mp hsource
  have ho := rankOrdered_of_orientation hw hs hv forward hori
  have hq := (List.pairwise_append.mp ho).1
  obtain ⟨mid, _, heq⟩ := placement_interleaving_of_orientation hw hs hv forward hori
  have hbound (x : Nat) (_ : x ∈ placement s) : frameRank w source forward x ≤ w + 1 :=
    branchRank_bound (cycleCoord_lt (by omega) forward)
  have he : complete (cycleAdjacent (2 * w + 1)) w s.1 pos =
      complete (cycleAdjacent (2 * w + 1)) bigger s.1 pos := by
    rcases hproper with hother | hpos
    · obtain ⟨last, tail, hsnd⟩ := List.exists_cons_of_ne_nil hother
      have hlast := congrArg List.getLast? heq
      simp only [placement, hsnd, List.reverse_cons, ← List.append_assoc,
        List.getLast?_append, List.getLast?_singleton] at hlast
      have hl : last = cycleLabel (2 * w + 1) source forward (w + 1) := Option.some.inj hlast
      have hnot : last ∉ s.1 := by
        have hnd := List.nodup_append.mp hv.placement_nodup
        intro hm
        exact hnd.2.2 last hm last (by simp [hsnd]) rfl
      have hb' (x : Nat) (hx : x ∈ s.1) : frameRank w source forward x ≤ w := by
        have hmem : x ∈ placement s := List.mem_append_left _ hx
        have hle := hbound x hmem
        have htop : frameRank w source forward x ≠ w + 1 := by
          intro ht
          have := (frameRank_top_iff (by omega) hs (hv.placement_mem.mp hmem) forward).mp ht
          subst x
          exact hnot (by simpa [hl] using hx)
        omega
      exact complete_budget_stable s.1 pos w bigger hq hb' (fun _ _ => by omega) (fun _ _ => by omega)
    · cases hfst : s.1 with
      | nil => simp [complete]
      | cons first tail =>
        have hhead := congrArg List.head? heq
        simp only [placement, hfst, List.cons_append, List.head?_cons, Option.some.injEq] at hhead
        have hnd : (first :: tail).Nodup := by
          simpa only [hfst] using (List.nodup_append.mp hv.placement_nodup).1
        rw [hfst] at hq
        have htail : ∀ x ∈ tail, 1 ≤ frameRank w source forward x := by
          intro x hx
          have hmem : x ∈ placement s := by simp [placement, hfst, hx]
          have hne : x ≠ source := by
            intro h
            subst x
            exact (List.nodup_cons.mp hnd).1 (by simpa [hhead] using hx)
          have := (frameRank_zero_iff hs (hv.placement_mem.mp hmem) forward).not.mpr hne
          omega
        have hstable := complete_budget_stable tail (pos - 1) w bigger (List.pairwise_cons.mp hq).2
          (fun x hx => hbound x (by simp [placement, hfst, hx]))
          (fun x hx => by have := htail x hx; omega) (fun x hx => by have := htail x hx; omega)
        rw [show pos = (pos - 1) + 1 by omega]
        simp only [complete, hstable]
  simp only [transition, Bool.false_eq_true, ↓reduceIte, he]

theorem balanced_changed_event_head {w bigger pos : Nat} {s : State} {side : Bool}
    (hw : 2 ≤ w) (hbig : w ≤ bigger) (hv : Valid (2 * w + 1) s) (hb : balanced w s = true)
    (hchanged : transition (cycleAdjacent (2 * w + 1)) w s side pos ≠
      transition (cycleAdjacent (2 * w + 1)) bigger s side pos) :
    pos = 0 ∧ (if side then s.1 = [] else s.2 = []) := by
  have first {t : State} (ht : Valid (2 * w + 1) t) (hbt : balanced w t = true)
      (hc : transition (cycleAdjacent (2 * w + 1)) w t false pos ≠
        transition (cycleAdjacent (2 * w + 1)) bigger t false pos) : pos = 0 ∧ t.2 = [] := by
    by_contra h
    have hp : t.2 ≠ [] ∨ pos ≠ 0 := by tauto
    exact hc (balanced_first_budget_stable hw hbig ht hbt pos hp)
  cases side with
  | false => exact first hv hb hchanged
  | true =>
    have hh := first hv.exchange (balanced_exchange hw hv hb)
    have he : transition (cycleAdjacent (2 * w + 1)) w (exchange s) false pos ≠
        transition (cycleAdjacent (2 * w + 1)) bigger (exchange s) false pos := by
      intro he
      apply hchanged
      have he' := congrArg (Option.map (fun e : Event => (exchange e.1, e.2))) he
      simpa [transition, exchange, Option.map_bind, Function.comp_def] using he'
    exact hh he

end OddCycle
