import OddCycle.FlowWords

/-! Completeness of the two changed incoming events at the paper's target. -/

namespace OddCycle

theorem changed_limited_head_to_target {w bigger initiating : Nat} {q : Queue}
    (hw : 2 ≤ w) (hbig : w < bigger) (hv : Valid (2 * w + 1) (q, []))
    (hb : balanced w (q, []) = true)
    (hc : complete (cycleAdjacent (2 * w + 1)) w q 0 ≠ complete (cycleAdjacent (2 * w + 1)) bigger q 0)
    (he : complete (cycleAdjacent (2 * w + 1)) w q 0 = some (flowQueue w, 0, initiating)) :
    q = flowWordX w ∧ initiating = w := by
  simp only [balanced, List.any_eq_true, beq_iff_eq] at hb
  obtain ⟨source, hsource, forward, _, ho⟩ := hb
  have hs := List.mem_range.mp hsource
  obtain ⟨mid, _, _, hlimited, _⟩ := balanced_changed_head_form hw hs hbig hv forward ho hc
  have hresult := hlimited.symm.trans he
  simp only [Option.some.injEq, Prod.mk.injEq] at hresult
  obtain ⟨hrest, hdep, hinit⟩ := hresult
  have hsource : source = w := by
    have hh := congrArg List.head? hrest
    simpa [flowQueue] using hh
  rw [hsource] at hs ho hdep hinit
  have hf : forward = false := by
    cases forward with
    | false => rfl
    | true => rw [(flow_endpoints hw).2.2.1] at hdep; omega
  subst forward
  have hi : initiating = w := hinit.symm
  rw [hi] at he ⊢
  refine ⟨?_, rfl⟩
  apply balanced_changed_head_injective hw hs hbig false hv (branchState_valid hw hs false) ho rfl hc
    (flowX_changed hw hbig)
  exact Or.inl (he.trans (flowX_complete hw hbig).1.symm)

theorem changed_unlimited_head_to_target {w bigger initiating : Nat} {q : Queue}
    (hw : 2 ≤ w) (hbig : w < bigger) (hv : Valid (2 * w + 1) (q, []))
    (hb : balanced w (q, []) = true)
    (hc : complete (cycleAdjacent (2 * w + 1)) w q 0 ≠ complete (cycleAdjacent (2 * w + 1)) bigger q 0)
    (he : complete (cycleAdjacent (2 * w + 1)) bigger q 0 = some (flowQueue w, 0, initiating)) :
    q = flowWordY w ∧ initiating = w := by
  simp only [balanced, List.any_eq_true, beq_iff_eq] at hb
  obtain ⟨source, hsource, forward, _, ho⟩ := hb
  have hs := List.mem_range.mp hsource
  obtain ⟨mid, _, _, _, hunlimited⟩ := balanced_changed_head_form hw hs hbig hv forward ho hc
  have hresult := hunlimited.symm.trans he
  simp only [Option.some.injEq, Prod.mk.injEq] at hresult
  obtain ⟨hrest, hdep, hinit⟩ := hresult
  have hsource : source = w := by
    have hh := congrArg List.head? hrest
    simpa [flowQueue] using hh
  rw [hsource] at hs ho hdep hinit
  have hf : forward = true := by
    cases forward with
    | false => rw [(flow_endpoints hw).2.1] at hdep; omega
    | true => rfl
  subst forward
  have hi : initiating = w := hinit.symm
  rw [hi] at he ⊢
  refine ⟨?_, rfl⟩
  apply balanced_changed_head_injective hw hs hbig true hv (flowY_frame hw).1 ho (flowY_frame hw).2 hc
    (flowY_changed hw hbig)
  exact Or.inr (he.trans (flowY_complete hw hbig).2.symm)

theorem flowQueue_length {w : Nat} (hw : 2 ≤ w) : (flowQueue w).length = 2 * w := by
  simp [flowQueue, flowCore, shortInterior]
  omega

theorem changed_incoming_queue {w bigger budget pos initiating : Nat} {s : State} {side : Bool}
    (hw : 2 ≤ w) (hbig : w < bigger) (hv : Valid (2 * w + 1) s) (hb : balanced w s = true)
    (hc : transition (cycleAdjacent (2 * w + 1)) w s side pos ≠
      transition (cycleAdjacent (2 * w + 1)) bigger s side pos)
    (he : transition (cycleAdjacent (2 * w + 1)) budget s side pos = some (flowTarget w, initiating)) :
    side = true ∧ pos = 0 ∧ s.1 = [] ∧
      complete (cycleAdjacent (2 * w + 1)) budget s.2 0 = some (flowQueue w, 0, initiating) := by
  obtain ⟨hpos, hother⟩ := balanced_changed_event_head hw hbig.le hv hb hc
  subst pos
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hother
    cases hcomp : complete (cycleAdjacent (2 * w + 1)) budget s.1 0 with
    | none => simp [transition, hcomp] at he
    | some result =>
      obtain ⟨rest, departed, init⟩ := result
      simp [transition, hcomp, flowTarget, hother] at he
      have hlen := congrArg List.length he.1.2
      rw [List.length_singleton, flowQueue_length hw] at hlen
      omega
  | true =>
    simp only [↓reduceIte] at hother
    refine ⟨rfl, rfl, hother, ?_⟩
    cases hcomp : complete (cycleAdjacent (2 * w + 1)) budget s.2 0 with
    | none => simp [transition, hcomp] at he
    | some result =>
      obtain ⟨rest, departed, init⟩ := result
      simp [transition, hcomp, flowTarget, hother] at he
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
      rfl

/-- Lemma 5: among changed events, exactly X is gained and exactly Y is lost.
Any comparison budget strictly greater than w gives the unlimited outputs. -/
theorem two_flow_completeness {w bigger pos initiating : Nat} {s : State} {side : Bool}
    (hw : 2 ≤ w) (hbig : w < bigger) (hv : Valid (2 * w + 1) s) (hb : balanced w s = true)
    (hc : transition (cycleAdjacent (2 * w + 1)) w s side pos ≠
      transition (cycleAdjacent (2 * w + 1)) bigger s side pos) :
    (transition (cycleAdjacent (2 * w + 1)) w s side pos = some (flowTarget w, initiating) ↔
      s = flowSourceX w ∧ side = true ∧ pos = 0 ∧ initiating = w) ∧
    (transition (cycleAdjacent (2 * w + 1)) bigger s side pos = some (flowTarget w, initiating) ↔
      s = flowSourceY w ∧ side = true ∧ pos = 0 ∧ initiating = w) := by
  have hqueue {budget : Nat}
      (he : transition (cycleAdjacent (2 * w + 1)) budget s side pos = some (flowTarget w, initiating)) :=
    changed_incoming_queue hw hbig hv hb hc he
  have hvalid (hempty : s.1 = []) : Valid (2 * w + 1) (s.2, []) := by
    simpa [exchange, hempty] using hv.exchange
  have hbalanced (hempty : s.1 = []) : balanced w (s.2, []) = true := by
    simpa [exchange, hempty] using balanced_exchange hw hv hb
  have hchanged (hempty : s.1 = []) (hside : side = true) (hpos : pos = 0) :
      complete (cycleAdjacent (2 * w + 1)) w s.2 0 ≠ complete (cycleAdjacent (2 * w + 1)) bigger s.2 0 := by
    intro he
    apply hc
    simp only [transition, hside, hpos, ↓reduceIte, he]
  constructor
  · constructor
    · intro he
      obtain ⟨hside, hpos, hempty, hcomp⟩ := hqueue he
      obtain ⟨hq, hi⟩ := changed_limited_head_to_target hw hbig (hvalid hempty) (hbalanced hempty)
        (hchanged hempty hside hpos) hcomp
      exact ⟨Prod.ext hempty hq, hside, hpos, hi⟩
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      simp [transition, flowSourceX, (flowX_complete hw hbig).1, flowTarget]
  · constructor
    · intro he
      obtain ⟨hside, hpos, hempty, hcomp⟩ := hqueue he
      obtain ⟨hq, hi⟩ := changed_unlimited_head_to_target hw hbig (hvalid hempty) (hbalanced hempty)
        (hchanged hempty hside hpos) hcomp
      exact ⟨Prod.ext hempty hq, hside, hpos, hi⟩
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      simp [transition, flowSourceY, (flowY_complete hw hbig).2, flowTarget]

end OddCycle
