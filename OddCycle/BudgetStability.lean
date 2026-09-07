import OddCycle.PlacementOrder

/-! A completion stops depending on its replacement budget once that budget
covers every possible strict increase of a topological rank. -/

namespace OddCycle

theorem carry_of_no_adj {adj : Nat → Nat → Bool} (budget job : Nat) (q : Queue)
    (h : ∀ x ∈ q, adj job x = false) : carry adj budget job q = (q, job) := by
  induction q with
  | nil => rfl
  | cons x xs ih =>
    simpa [carry, h x (by simp)] using
      (show (if budget = 0 then (x :: xs, job)
        else (x :: (carry adj budget job xs).1, (carry adj budget job xs).2)) = (x :: xs, job) by
          rw [ih (fun y hy => h y (by simp [hy]))]
          split <;> rfl)

theorem carry_budget_stable {adj : Nat → Nat → Bool} {rank : Nat → Nat} {bound : Nat}
    (q : Queue) (job first second : Nat)
    (ho : RankOrdered adj rank (job :: q)) (hb : ∀ x ∈ job :: q, rank x ≤ bound)
    (hfirst : bound ≤ first + rank job) (hsecond : bound ≤ second + rank job) :
    carry adj first job q = carry adj second job q := by
  induction q generalizing job first second with
  | nil => rfl
  | cons x xs ih =>
    have hp := List.pairwise_cons.mp ho
    by_cases hz : first = 0 ∨ second = 0
    · have hno : ∀ y ∈ x :: xs, adj job y = false := by
        intro y hy
        by_cases ha : adj job y = true
        · have hlt := hp.1 y hy ha
          have hle := hb y (by simp [hy])
          rcases hz with hz | hz <;> omega
        · exact Bool.eq_false_iff.mpr ha
      rw [carry_of_no_adj first job _ hno, carry_of_no_adj second job _ hno]
    · have hf : first ≠ 0 := fun h => hz (Or.inl h)
      have hs : second ≠ 0 := fun h => hz (Or.inr h)
      by_cases ha : adj job x = true
      · have hr := hp.1 x (by simp) ha
        have he := ih x (first - 1) (second - 1) hp.2
          (fun y hy => hb y (by simp [hy])) (by omega) (by omega)
        simp only [carry, hf, hs, if_false, ha, if_true, he]
      · have he := ih job first second
          (List.pairwise_cons.mpr ⟨fun y hy => hp.1 y (by simp [hy]),
            (List.pairwise_cons.mp hp.2).2⟩)
          (fun y hy => hb y (by
            rcases List.mem_cons.mp hy with rfl | hy
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))) hfirst hsecond
        simp [carry, hf, hs, ha, he]

theorem complete_budget_stable {adj : Nat → Nat → Bool} {rank : Nat → Nat} {bound : Nat}
    (q : Queue) (pos first second : Nat)
    (ho : RankOrdered adj rank q) (hb : ∀ x ∈ q, rank x ≤ bound)
    (hfirst : ∀ x ∈ q, bound ≤ first + rank x)
    (hsecond : ∀ x ∈ q, bound ≤ second + rank x) :
    complete adj first q pos = complete adj second q pos := by
  induction q generalizing pos with
  | nil => rfl
  | cons x xs ih =>
    cases pos with
    | zero =>
      simp only [complete, carry_budget_stable xs x first second ho hb
        (hfirst x (by simp)) (hsecond x (by simp))]
    | succ pos =>
      have he := ih pos (List.pairwise_cons.mp ho).2
        (fun y hy => hb y (by simp [hy]))
        (fun y hy => hfirst y (by simp [hy])) (fun y hy => hsecond y (by simp [hy]))
      simp only [complete, he]

/-- A budget at least the untouched suffix length is literally unlimited. -/
theorem carry_budget_stable_of_length (adj : Nat → Nat → Bool) (q : Queue)
    (job first second : Nat) (hf : q.length ≤ first) (hs : q.length ≤ second) :
    carry adj first job q = carry adj second job q := by
  induction q generalizing job first second with
  | nil => rfl
  | cons x xs ih =>
    have hf' : first ≠ 0 := by simp only [List.length_cons] at hf; omega
    have hs' : second ≠ 0 := by simp only [List.length_cons] at hs; omega
    by_cases ha : adj job x = true
    · have he := ih x (first - 1) (second - 1)
        (by simp only [List.length_cons] at hf; omega)
        (by simp only [List.length_cons] at hs; omega)
      simp only [carry, hf', hs', if_false, ha, if_true, he]
    · have he := ih job first second
        (by simp only [List.length_cons] at hf; omega)
        (by simp only [List.length_cons] at hs; omega)
      simp [carry, hf', hs', ha, he]

end OddCycle
