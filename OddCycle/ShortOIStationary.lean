import OddCycle.OIStationary
import OddCycle.CycleRecurrenceClassification

/-! Canonical OI balance on each short orientation class. -/

namespace OddCycle

theorem complete_short_budgets {adj : Nat → Nat → Bool} {w v : Nat} {q : Queue}
    (hw : PathsBounded adj w q) (hv : PathsBounded adj v q) (pos : Nat) :
    complete adj w q pos = complete adj v q pos := by
  induction q generalizing pos with
  | nil => rfl
  | cons a q ih =>
    cases pos with
    | zero =>
      have cw := carry_eq_unlimited_of_paths q a w (by
        intro p hp he
        have hh := hw (a :: p) (hp.cons_cons a) he
        simp only [List.length_cons] at hh
        omega)
      have cv := carry_eq_unlimited_of_paths q a v (by
        intro p hp he
        have hh := hv (a :: p) (hp.cons_cons a) he
        simp only [List.length_cons] at hh
        omega)
      simp only [complete, cw, cv]
    | succ pos =>
      simp only [complete, ih (hw.sublist (List.sublist_cons_self a q))
        (hv.sublist (List.sublist_cons_self a q)) pos]

theorem transition_short_unlimited {n w : Nat} {s : State} (hs : Valid n s)
    (hh : height n s ≤ w) (side : Bool) (pos : Nat) :
    transition (cycleAdjacent n) w s side pos = transition (cycleAdjacent n) n s side pos := by
  have hb : height n s ≤ n := (height_le_population hs).trans (by omega)
  have bound (v : Nat) (hv : height n s ≤ v) :
      PathsBounded (cycleAdjacent n) v (if side then s.2 else s.1) := by
    cases side with
    | false => exact (pathsBounded_iff_height.mpr hv).sublist (List.sublist_append_left _ _)
    | true => simpa only [List.reverse_reverse] using
        ((pathsBounded_iff_height.mpr hv).sublist
          (List.sublist_append_right _ _)).reverse (cycleAdjacent_symm n)
  simp only [transition, complete_short_budgets (bound w hh) (bound n hb) pos]

theorem incomingOccurrences_short {n w : Nat} {states : List State}
    (hs : ∀ s ∈ states, Valid n s ∧ height n s ≤ w) (target : State) :
    incomingOccurrences (cycleAdjacent n) w states target = incomingOccurrences (cycleAdjacent n) n states target := by
  unfold incomingOccurrences
  simp only [List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro s hmem
  have he := transition_short_unlimited (hs s hmem).1 (hs s hmem).2
  apply congrArg (fun f => (positions s).filterMap f)
  funext p
  unfold selectIncoming
  rw [he p.1 p.2]

theorem short_oi_stationary {K : Type*} [Field K] {n w : Nat} {states : List State}
    (hn : 0 < n) (hs : OrientationSupport n states) (hshort : ∀ s ∈ states, height n s ≤ w)
    (μ ν : OICapacity K) (hμ : μ.Regular (List.range n)) (hν : ν.Regular (List.range n)) :
    OIStationary (cycleAdjacent n) w μ ν states (oiCanonicalWeight μ ν) := by
  intro target ht
  have he := unlimited_oi_stationary hn hs μ ν hμ hν target ht
  unfold oiBalance at he ⊢
  rw [incomingOccurrences_short (fun s hs' => ⟨hs.valid s hs', hshort s hs'⟩)]
  exact he

theorem positive_short_oi_stationary {n w : Nat} {states : List State}
    (hn : 0 < n) (hs : OrientationSupport n states) (hshort : ∀ s ∈ states, height n s ≤ w)
    (μ ν : PositiveOIAllocation n) :
    OIStationary (cycleAdjacent n) w μ.toOICapacity ν.toOICapacity states
      (oiCanonicalWeight μ.toOICapacity ν.toOICapacity) :=
  short_oi_stationary hn hs hshort _ _ μ.regular ν.regular

end OddCycle
