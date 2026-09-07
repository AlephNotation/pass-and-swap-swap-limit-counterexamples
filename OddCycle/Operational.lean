import OddCycle.Model

/-! Structural facts about the operational rule, for arbitrary populations,
graphs, completion positions, and replacement budgets. -/

namespace OddCycle

theorem carry_population (adj : Nat → Nat → Bool) (budget job : Nat) (q : Queue) :
    ((carry adj budget job q).1 ++ [(carry adj budget job q).2]).Perm (job :: q) := by
  induction q generalizing budget job with
  | nil => simp [carry]
  | cons x xs ih =>
    by_cases hz : budget = 0
    · simp only [carry, hz, if_true]
      exact List.perm_append_comm
    · by_cases ha : adj job x = true
      · simpa [carry, hz, ha] using (ih (budget - 1) x).cons job
      · simpa [carry, hz, ha] using
          ((ih budget job).cons x).trans (List.Perm.swap job x xs)

theorem complete_population {adj : Nat → Nat → Bool} {budget pos : Nat}
    {q rest : Queue} {departed initiating : Nat}
    (h : complete adj budget q pos = some (rest, departed, initiating)) :
    (rest ++ [departed]).Perm q := by
  induction q generalizing pos rest departed initiating with
  | nil => simp [complete] at h
  | cons x xs ih =>
    cases pos with
    | zero =>
      simp only [complete, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hr, hd, _⟩ := h
      subst rest
      subst departed
      exact carry_population adj budget x xs
    | succ pos =>
      cases he : complete adj budget xs pos with
      | none => simp [complete, he] at h
      | some result =>
        obtain ⟨r, d, i⟩ := result
        simp [complete, he] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        exact (ih he).cons x

theorem transition_population {adj : Nat → Nat → Bool} {budget pos : Nat}
    {s t : State} {side : Bool} {initiating : Nat}
    (h : transition adj budget s side pos = some (t, initiating)) :
    (t.1 ++ t.2).Perm (s.1 ++ s.2) := by
  cases side with
  | false =>
    cases he : complete adj budget s.1 pos with
    | none => simp [transition, he] at h
    | some result =>
      obtain ⟨r, d, i⟩ := result
      simp [transition, he] at h
      rcases h with ⟨rfl, rfl⟩
      have hc := complete_population he
      exact ((List.perm_append_comm : (s.2 ++ [d]).Perm ([d] ++ s.2)).append_left r).trans
        (by simpa [List.append_assoc] using hc.append_right s.2)
  | true =>
    cases he : complete adj budget s.2 pos with
    | none => simp [transition, he] at h
    | some result =>
      obtain ⟨r, d, i⟩ := result
      simp [transition, he] at h
      rcases h with ⟨rfl, rfl⟩
      have hc := complete_population he
      exact (by simpa [List.append_assoc] using
        ((List.perm_append_comm : ([d] ++ r).Perm (r ++ [d])).trans hc).append_left s.1)

theorem transition_valid {n budget pos : Nat} {adj : Nat → Nat → Bool}
    {s t : State} {side : Bool} {initiating : Nat} (hs : Valid n s)
    (h : transition adj budget s side pos = some (t, initiating)) : Valid n t :=
  (transition_population h).trans hs

end OddCycle
