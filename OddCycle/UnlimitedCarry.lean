import OddCycle.BudgetStability

/-! An unbounded scan and its inverse. Equality with the original budgeted
rule is proved whenever the budget covers the untouched suffix length. -/

namespace OddCycle

def unlimitedCarry (adj : Nat → Nat → Bool) (job : Nat) : Queue → Queue × Nat
  | [] => ([], job)
  | x :: xs =>
    if adj job x then
      let result := unlimitedCarry adj x xs
      (job :: result.1, result.2)
    else
      let result := unlimitedCarry adj job xs
      (x :: result.1, result.2)

theorem carry_eq_unlimited (adj : Nat → Nat → Bool) (q : Queue) (job budget : Nat)
    (hbudget : q.length ≤ budget) : carry adj budget job q = unlimitedCarry adj job q := by
  induction q generalizing job budget with
  | nil => rfl
  | cons x xs ih =>
    have hz : budget ≠ 0 := by simp only [List.length_cons] at hbudget; omega
    by_cases ha : adj job x = true
    · have he := ih x (budget - 1) (by simp only [List.length_cons] at hbudget; omega)
      simp [carry, unlimitedCarry, hz, ha, he]
    · have he := ih job budget (by simp only [List.length_cons] at hbudget; omega)
      simp [carry, unlimitedCarry, hz, ha, he]

theorem unlimitedCarry_append (adj : Nat → Nat → Bool) (q tail : Queue) (job : Nat) :
    unlimitedCarry adj job (q ++ tail) =
      ((unlimitedCarry adj job q).1 ++ (unlimitedCarry adj (unlimitedCarry adj job q).2 tail).1,
        (unlimitedCarry adj (unlimitedCarry adj job q).2 tail).2) := by
  induction q generalizing job with
  | nil => rfl
  | cons x xs ih =>
    by_cases ha : adj job x = true <;> simp [unlimitedCarry, ha, ih]

theorem unlimitedCarry_inverse {adj : Nat → Nat → Bool}
    (hsym : ∀ x y, adj x y = adj y x) (q : Queue) (job : Nat) :
    unlimitedCarry adj (unlimitedCarry adj job q).2 (unlimitedCarry adj job q).1.reverse =
      (q.reverse, job) := by
  induction q generalizing job with
  | nil => rfl
  | cons x xs ih =>
    by_cases ha : adj job x = true
    · have hrev : adj x job = true := by simpa only [hsym x job] using ha
      simp only [unlimitedCarry, ha, if_true, List.reverse_cons, unlimitedCarry_append, ih]
      simp [hrev]
    · simp [unlimitedCarry, ha, unlimitedCarry_append, ih]

theorem unlimitedCarry_population (adj : Nat → Nat → Bool) (q : Queue) (job : Nat) :
    ((unlimitedCarry adj job q).1 ++ [(unlimitedCarry adj job q).2]).Perm (job :: q) := by
  rw [← carry_eq_unlimited adj q job q.length (Nat.le_refl _)]
  exact carry_population adj q.length job q

theorem unlimitedCarry_length (adj : Nat → Nat → Bool) (q : Queue) (job : Nat) :
    (unlimitedCarry adj job q).1.length = q.length := by
  have h := (unlimitedCarry_population adj q job).length_eq
  simpa using h

theorem unlimitedCarry_edgeEquiv {adj : Nat → Nat → Bool}
    (hsym : ∀ x y, adj x y = adj y x) (q : Queue) (job : Nat) :
    EdgeEquiv adj (job :: q) ((unlimitedCarry adj job q).1 ++ [(unlimitedCarry adj job q).2]) := by
  induction q generalizing job with
  | nil => exact EdgeEquiv.refl _ _
  | cons x xs ih =>
    by_cases ha : adj job x = true
    · simpa [unlimitedCarry, ha] using (ih x).cons job
    · have hh := (edgeEquiv_swap hsym (Bool.eq_false_iff.mpr ha) xs).trans ((ih job).cons x)
      simpa [unlimitedCarry, ha] using hh

end OddCycle
