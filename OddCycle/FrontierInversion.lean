import OddCycle.CompletionFrontier

/-! Reconstructing the input of a truncated scan from its processed prefix.
This retains the stopping position needed to count changed predecessors. -/

namespace OddCycle

theorem scanFrontier_unlimited_prefix (adj : Nat → Nat → Bool) (q : Queue) (w job : Nat) :
    let f := scanFrontier adj w job q
    unlimitedCarry adj job (q.take f.processed.length) = (f.processed, f.carried) ∧
      q.drop f.processed.length = f.untouched := by
  induction q generalizing w job with
  | nil => simp [scanFrontier, unlimitedCarry]
  | cons x xs ih =>
    by_cases hz : w = 0
    · simp [scanFrontier, hz, unlimitedCarry]
    · by_cases ha : adj job x = true
      · have hh := ih (w - 1) x
        simp only [scanFrontier, hz, if_false, ha, if_true, List.length_cons,
          List.take_succ_cons, List.drop_succ_cons, unlimitedCarry, hh.1, hh.2, and_self]
      · have hh := ih w job
        simp [scanFrontier, hz, ha, unlimitedCarry, hh.1, hh.2]

theorem scanFrontier_unlimited_continuation (adj : Nat → Nat → Bool) (q : Queue) (w job : Nat) :
    let f := scanFrontier adj w job q
    unlimitedCarry adj job q =
      (f.processed ++ (unlimitedCarry adj f.carried f.untouched).1,
        (unlimitedCarry adj f.carried f.untouched).2) := by
  have hh := scanFrontier_unlimited_prefix adj q w job
  have he := unlimitedCarry_append adj (q.take (scanFrontier adj w job q).processed.length)
    (q.drop (scanFrontier adj w job q).processed.length) job
  rw [List.take_append_drop] at he
  simpa only [hh.1, hh.2] using he

theorem scanFrontier_reconstruct {adj : Nat → Nat → Bool} (hsym : ∀ a b, adj a b = adj b a)
    (q : Queue) (w job : Nat) :
    let f := scanFrontier adj w job q
    job :: q =
      (unlimitedCarry adj f.carried f.processed.reverse).2 ::
        (unlimitedCarry adj f.carried f.processed.reverse).1.reverse ++ f.untouched := by
  have hh := scanFrontier_unlimited_prefix adj q w job
  have hi := unlimitedCarry_inverse hsym (q.take (scanFrontier adj w job q).processed.length) job
  rw [hh.1] at hi
  dsimp only at hi ⊢
  rw [hi]
  simp only [List.reverse_reverse, ← hh.2, List.cons_append, List.take_append_drop]

theorem scanFrontier_processed_last {adj : Nat → Nat → Bool} {q : Queue} {w job : Nat}
    (hw : 0 < w) (ht : (scanFrontier adj w job q).untouched ≠ []) :
    ∃ pre previous, (scanFrontier adj w job q).processed = pre ++ [previous] ∧
      adj previous (scanFrontier adj w job q).carried = true := by
  induction q generalizing w job with
  | nil => simp [scanFrontier] at ht
  | cons x xs ih =>
    have hz : w ≠ 0 := by omega
    by_cases ha : adj job x = true
    · by_cases hone : w = 1
      · subst w
        cases xs with
        | nil => exact ⟨[], job, by simp [scanFrontier, ha], by simp [scanFrontier, ha]⟩
        | cons y ys => exact ⟨[], job, by simp [scanFrontier, ha], by simp [scanFrontier, ha]⟩
      · have ht' : (scanFrontier adj (w - 1) x xs).untouched ≠ [] := by
          simpa only [scanFrontier, hz, if_false, ha, if_true] using ht
        obtain ⟨pre, previous, hp, he⟩ := ih (by omega : 0 < w - 1) ht'
        exact ⟨job :: pre, previous, by simp only [scanFrontier, hz, if_false, ha, if_true, hp, List.cons_append],
          by simpa only [scanFrontier, hz, if_false, ha, if_true] using he⟩
    · have ht' : (scanFrontier adj w job xs).untouched ≠ [] := by
        simpa only [scanFrontier, hz, if_false, ha] using ht
      obtain ⟨pre, previous, hp, he⟩ := ih hw ht'
      exact ⟨x :: pre, previous, by simp [scanFrontier, hz, ha, hp],
        by simpa only [scanFrontier, hz, if_false, ha] using he⟩

theorem complete_split {adj : Nat → Nat → Bool} {w pos init departed : Nat} {q rest : Queue}
    (he : complete adj w q pos = some (rest, departed, init)) :
    ∃ pre tail out, q = pre ++ init :: tail ∧ pre.length = pos ∧ rest = pre ++ out ∧
      carry adj w init tail = (out, departed) := by
  induction q generalizing pos rest with
  | nil => simp [complete] at he
  | cons x xs ih =>
    cases pos with
    | zero =>
      simp only [complete, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hr, hd, hi⟩ := he
      subst init
      exact ⟨[], xs, rest, by simp, rfl, by simp, Prod.ext hr hd⟩
    | succ pos =>
      cases hc : complete adj w xs pos with
      | none => simp [complete, hc] at he
      | some result =>
        obtain ⟨r, d, i⟩ := result
        simp [complete, hc] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        obtain ⟨pre, tail, out, hq, hp, hr, hout⟩ := ih hc
        exact ⟨x :: pre, tail, out, by simp [hq], by simp [hp], by simp [hr], hout⟩

theorem scanFrontier_chain_le_processed (adj : Nat → Nat → Bool) (q : Queue) (w job : Nat) :
    (scanFrontier adj w job q).chain.length ≤ (scanFrontier adj w job q).processed.length + 1 := by
  induction q generalizing w job with
  | nil => simp [scanFrontier]
  | cons x xs ih =>
    by_cases hz : w = 0
    · simp [scanFrontier, hz]
    · by_cases ha : adj job x = true
      · have hh := ih (w - 1) x
        simp only [scanFrontier, hz, if_false, ha, if_true, List.length_cons]
        omega
      · have hh := ih w job
        simpa [scanFrontier, hz, ha] using hh.trans (by omega)

theorem scanFrontier_untouched_of_changed {adj : Nat → Nat → Bool} {q : Queue} {w job : Nat}
    (h : carry adj w job q ≠ unlimitedCarry adj job q) :
    (scanFrontier adj w job q).untouched ≠ [] := by
  intro he
  apply h
  rw [scanFrontier_result, scanFrontier_unlimited_continuation adj q w job]
  simp [he, unlimitedCarry]

/-- A changed incoming event is determined by its original initiating
position and the prefix where its final replacement stopped. -/
theorem changed_complete_reconstruct {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) {w big pos init departed : Nat} {q rest : Queue}
    (hw : 0 < w) (hbig : q.length ≤ big)
    (he : complete adj w q pos = some (rest, departed, init))
    (hne : complete adj big q pos ≠ some (rest, departed, init)) :
    ∃ pre processed untouched previous,
      rest = pre ++ processed ++ untouched ∧ pre.length = pos ∧ untouched ≠ [] ∧
      w ≤ processed.length ∧ processed.getLast? = some previous ∧ adj previous departed = true ∧
      q = pre ++ (unlimitedCarry adj departed processed.reverse).2 ::
        (unlimitedCarry adj departed processed.reverse).1.reverse ++ untouched := by
  obtain ⟨pre, tail, out, hq, hp, hr, hc⟩ := complete_split he
  have hchange : carry adj w init tail ≠ unlimitedCarry adj init tail := by
    intro hh
    apply hne
    have hlen : tail.length ≤ big := by simp only [hq, List.length_append, List.length_cons] at hbig; omega
    have hcb : carry adj big init tail = (out, departed) := by
      rw [carry_eq_unlimited adj tail init big hlen, ← hh, hc]
    have hcomp : complete adj big (init :: tail) 0 = some (out, departed, init) := by simp [complete, hcb]
    simpa only [hq, hp, Nat.add_zero, ← hr] using complete_append pre hcomp
  let f := scanFrontier adj w init tail
  have htail : f.untouched ≠ [] := scanFrontier_untouched_of_changed hchange
  have hcarried : f.carried = departed := by
    have hh := congrArg Prod.snd (hc.symm.trans (scanFrontier_result adj tail w init))
    exact hh.symm
  have hout : out = f.processed ++ f.untouched :=
    congrArg Prod.fst (hc.symm.trans (scanFrontier_result adj tail w init))
  have hlen := scanFrontier_chain_le_processed adj tail w init
  have hex := scanFrontier_exhausted adj tail w init htail
  obtain ⟨p, previous, hlast, hadj⟩ := scanFrontier_processed_last hw htail
  refine ⟨pre, f.processed, f.untouched, previous, ?_, hp, htail, ?_, ?_, ?_, ?_⟩
  · rw [hr, hout, List.append_assoc]
  · change w ≤ f.processed.length
    change f.chain.length ≤ f.processed.length + 1 at hlen
    change f.chain.length = w + 1 at hex
    omega
  · change f.processed = p ++ [previous] at hlast
    rw [hlast]
    simp
  · change adj previous f.carried = true at hadj
    simpa only [hcarried] using hadj
  · have hi := scanFrontier_reconstruct hsym tail w init
    change init :: tail = (unlimitedCarry adj f.carried f.processed.reverse).2 ::
      (unlimitedCarry adj f.carried f.processed.reverse).1.reverse ++ f.untouched at hi
    rw [hq, hi, hcarried]
    simp only [List.append_assoc]

end OddCycle
