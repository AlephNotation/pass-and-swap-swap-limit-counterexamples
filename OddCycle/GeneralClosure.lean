import OddCycle.BalancedSymmetry

/-! Allocation-independent balanced-region closure. No finite enumeration,
stationary certificate, or unlimited product-form theorem is used here. -/

namespace OddCycle

theorem balanced_transition_first {w : Nat} (hw : 2 ≤ w) {s t : State}
    (hv : Valid (2 * w + 1) s) (hb : balanced w s = true) {pos initiating : Nat}
    (h : transition (cycleAdjacent (2 * w + 1)) w s false pos = some (t, initiating)) :
    balanced w t = true := by
  have hn : 0 < 2 * w + 1 := by omega
  have ht := transition_valid hv h
  simp only [balanced, List.any_eq_true, beq_iff_eq] at hb
  obtain ⟨source, hsource, forward, _, hori⟩ := hb
  have hs := List.mem_range.mp hsource
  change orientation (2 * w + 1) s = orientation (2 * w + 1) (branchState w source forward) at hori
  let p := cycleLabel (2 * w + 1) source forward w
  let v := cycleLabel (2 * w + 1) source forward (w + 1)
  have hp : p < 2 * w + 1 := cycleLabel_lt hn forward
  have hvl : v < 2 * w + 1 := cycleLabel_lt hn forward
  have hpv : p ≠ v := by
    intro heq
    have hh := cycleLabel_injective hs (show w < 2 * w + 1 by omega)
      (show w + 1 < 2 * w + 1 by omega) forward heq
    omega
  have hidx : (placement t).idxOf p ≠ (placement t).idxOf v :=
    (List.idxOf_inj (ht.placement_mem.mpr hp)).not.mpr hpv
  have hzero := branchState_boundary_before hw hs forward
  have hone := branchState_flip_boundary_before hw hs forward
  change (placement (branchState w source forward)).idxOf p <
    (placement (branchState w source forward)).idxOf v at hzero
  change (placement (branchState w source (!forward))).idxOf v <
    (placement (branchState w source (!forward))).idxOf p at hone
  have he : EdgeEquiv (eraseEdge (cycleAdjacent (2 * w + 1)) p v) (placement s) (placement t) := by
    apply transition_first_edgeEquiv_erase (rank := frameRank w source forward)
      (allowed := fun x => x < 2 * w + 1) (cycleAdjacent_symm (2 * w + 1))
    · intro a b ha hb hhigh hup _
      exact Or.inl (frameRank_boundary hs ha hb forward hhigh hup)
    · intro x hx
      exact hv.placement_mem.mp (List.mem_append_left _ hx)
    · exact rankOrdered_of_orientation hw hs hv forward hori
    · exact h
  have hcommon (a b : Nat) (ha : a < 2 * w + 1) (hb : b < 2 * w + 1)
      (hab : cycleAdjacent (2 * w + 1) a b = true)
      (hex : ¬ ((a = p ∧ b = v) ∨ (a = v ∧ b = p))) :
      (placement t).idxOf a < (placement t).idxOf b ↔
        (placement (branchState w source forward)).idxOf a <
          (placement (branchState w source forward)).idxOf b := by
    have hreduced : eraseEdge (cycleAdjacent (2 * w + 1)) p v a b = true := by
      simp [eraseEdge, hab]
      tauto
    exact (he.before_iff hreduced).symm.trans
      (orientation_before_iff hv (branchState_valid hw hs forward) hori ha hb hab)
  by_cases hbefore : (placement t).idxOf p < (placement t).idxOf v
  · apply balanced_of_orientation_eq (t := branchState w source forward)
    · apply orientation_eq_of_except hn (p := p) (v := v)
      · exact iff_of_true hbefore hzero
      · change (placement t).idxOf v < (placement t).idxOf p ↔ _
        omega
      · exact hcommon
    · exact branchState_balanced hs forward
  · apply balanced_of_orientation_eq (t := branchState w source (!forward))
    · apply orientation_eq_of_except hn (p := p) (v := v)
      · change (placement t).idxOf p < (placement t).idxOf v ↔ _
        omega
      · change (placement t).idxOf v < (placement t).idxOf p ↔ _
        have hvp : (placement t).idxOf v < (placement t).idxOf p := by omega
        exact iff_of_true hvp hone
      · intro a b ha hb hab hex
        exact (hcommon a b ha hb hab hex).trans (branchState_flip_before hw hs ha hb hab forward hex)
    · exact branchState_balanced hs (!forward)

theorem balanced_transition {w : Nat} (hw : 2 ≤ w) {s t : State}
    (hv : Valid (2 * w + 1) s) (hb : balanced w s = true)
    {second : Bool} {pos initiating : Nat}
    (h : transition (cycleAdjacent (2 * w + 1)) w s second pos = some (t, initiating)) :
    balanced w t = true := by
  cases second
  · exact balanced_transition_first hw hv hb h
  · have ht := transition_valid hv h
    have he := balanced_transition_first hw hv.exchange (balanced_exchange hw hv hb)
      (transition_exchange h)
    simpa only [exchange_exchange] using balanced_exchange hw ht.exchange he

/-- General closure under every queue-position completion, independently of
the completion rates. The fixed population is preserved as well. -/
theorem balanced_events_closed {w : Nat} (hw : 2 ≤ w) {s : State}
    (hv : Valid (2 * w + 1) s) (hb : balanced w s = true) {e : Event}
    (he : e ∈ events (cycleAdjacent (2 * w + 1)) w s) :
    Valid (2 * w + 1) e.1 ∧ balanced w e.1 = true := by
  rcases e with ⟨t, initiating⟩
  simp only [events, List.mem_append, List.mem_filterMap] at he
  rcases he with ⟨pos, _, h⟩ | ⟨pos, _, h⟩
  · exact ⟨transition_valid hv h, balanced_transition hw hv hb h⟩
  · exact ⟨transition_valid hv h, balanced_transition hw hv hb h⟩

/-- The nonemptiness and closure assertions of manuscript Lemma 2 for every
odd cycle C_(2w+1), w ≥ 2. -/
theorem balanced_region_nonempty_closed {w : Nat} (hw : 2 ≤ w) :
    (∃ s, Valid (2 * w + 1) s ∧ balanced w s = true) ∧
    (∀ s, Valid (2 * w + 1) s → balanced w s = true →
      ∀ e ∈ events (cycleAdjacent (2 * w + 1)) w s,
        Valid (2 * w + 1) e.1 ∧ balanced w e.1 = true) :=
  ⟨balanced_nonempty hw, fun _ hv hb _ he => balanced_events_closed hw hv hb he⟩

end OddCycle
