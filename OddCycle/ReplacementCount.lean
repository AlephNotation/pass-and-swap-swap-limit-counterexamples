import OddCycle.UnlimitedPredecessors

/-! Exact replacement counts for unlimited scans, their inverses, and
truncation. Distinct jobs make an early departure detectably different. -/

namespace OddCycle

def replacementCount (adj : Nat → Nat → Bool) (job : Nat) : Queue → Nat
  | [] => 0
  | x :: xs => if adj job x then replacementCount adj x xs + 1 else replacementCount adj job xs

theorem replacementCount_append (adj : Nat → Nat → Bool) (q tail : Queue) (job : Nat) :
    replacementCount adj job (q ++ tail) = replacementCount adj job q +
      replacementCount adj (unlimitedCarry adj job q).2 tail := by
  induction q generalizing job with
  | nil => simp [replacementCount, unlimitedCarry]
  | cons x xs ih =>
    by_cases ha : adj job x = true <;> simp [replacementCount, unlimitedCarry, ha, ih]
    omega

theorem replacementCount_inverse {adj : Nat → Nat → Bool} (hsym : ∀ a b, adj a b = adj b a)
    (q : Queue) (job : Nat) :
    replacementCount adj (unlimitedCarry adj job q).2 (unlimitedCarry adj job q).1.reverse =
      replacementCount adj job q := by
  induction q generalizing job with
  | nil => rfl
  | cons x xs ih =>
    by_cases ha : adj job x = true
    · have hr : adj x job = true := by simpa only [hsym x job] using ha
      simp [unlimitedCarry, replacementCount, ha, List.reverse_cons, replacementCount_append,
        unlimitedCarry_inverse hsym, ih, hr]
    · have hr : adj job x = false := Bool.eq_false_iff.mpr ha
      simp [unlimitedCarry, replacementCount, hr, replacementCount_append,
        unlimitedCarry_inverse hsym, ih]

theorem carry_eq_unlimited_of_count (adj : Nat → Nat → Bool) (q : Queue) (w job : Nat)
    (h : replacementCount adj job q ≤ w) : carry adj w job q = unlimitedCarry adj job q := by
  induction q generalizing w job with
  | nil => rfl
  | cons x xs ih =>
    by_cases ha : adj job x = true
    · have hc : replacementCount adj x xs + 1 ≤ w := by simpa [replacementCount, ha] using h
      have hw : w ≠ 0 := by omega
      simp [carry, unlimitedCarry, ha, hw, ih (w - 1) x (by omega)]
    · have hc : replacementCount adj job xs ≤ w := by simpa [replacementCount, ha] using h
      by_cases hw : w = 0
      · subst w
        have hh := ih 0 job hc
        rw [carry_zero] at hh
        simp [carry, unlimitedCarry, ha, ← hh]
      · simp [carry, unlimitedCarry, ha, hw, ih w job hc]

theorem unlimited_departed_mem (adj : Nat → Nat → Bool) (q : Queue) (job : Nat) :
    (unlimitedCarry adj job q).2 ∈ job :: q := by
  exact (unlimitedCarry_population adj q job).mem_iff.mp (by simp)

theorem unlimited_departed_mem_of_positive {adj : Nat → Nat → Bool} {q : Queue} {job : Nat}
    (h : 0 < replacementCount adj job q) : (unlimitedCarry adj job q).2 ∈ q := by
  induction q generalizing job with
  | nil => simp [replacementCount] at h
  | cons x xs ih =>
    by_cases ha : adj job x = true
    · simpa only [unlimitedCarry, ha, if_true] using unlimited_departed_mem adj xs x
    · have hc : 0 < replacementCount adj job xs := by simpa [replacementCount, ha] using h
      simpa [unlimitedCarry, ha] using List.mem_cons_of_mem x (ih hc)

theorem departed_ne_of_count_lt {adj : Nat → Nat → Bool} {q : Queue} {w job : Nat}
    (hnd : (job :: q).Nodup) (h : w < replacementCount adj job q) :
    (carry adj w job q).2 ≠ (unlimitedCarry adj job q).2 := by
  induction q generalizing w job with
  | nil => simp [replacementCount] at h
  | cons x xs ih =>
    by_cases hw : w = 0
    · subst w
      have hm := unlimited_departed_mem_of_positive h
      simpa only [carry, if_true] using (fun he => (List.nodup_cons.mp hnd).1 (he ▸ hm) :
        job ≠ (unlimitedCarry adj job (x :: xs)).2)
    · by_cases ha : adj job x = true
      · have hc : w - 1 < replacementCount adj x xs := by simp [replacementCount, ha] at h; omega
        simpa [carry, unlimitedCarry, hw, ha] using ih (List.nodup_cons.mp hnd).2 hc
      · have hc : w < replacementCount adj job xs := by simpa [replacementCount, ha] using h
        have hd : (job :: xs).Nodup := hnd.sublist ((List.sublist_cons_self x xs).cons_cons job)
        simpa [carry, unlimitedCarry, hw, ha] using ih hd hc

theorem carry_eq_unlimited_iff_count {adj : Nat → Nat → Bool} {q : Queue} {w job : Nat}
    (hnd : (job :: q).Nodup) :
    carry adj w job q = unlimitedCarry adj job q ↔ replacementCount adj job q ≤ w := by
  constructor
  · intro he
    by_contra h
    exact departed_ne_of_count_lt hnd (Nat.lt_of_not_ge h) (congrArg Prod.snd he)
  · exact carry_eq_unlimited_of_count adj q w job

theorem carry_append_of_count {adj : Nat → Nat → Bool} (q tail : Queue) (w job : Nat)
    (hw : replacementCount adj job q ≤ w) :
    carry adj w job (q ++ tail) =
      ((unlimitedCarry adj job q).1 ++
        (carry adj (w - replacementCount adj job q) (unlimitedCarry adj job q).2 tail).1,
        (carry adj (w - replacementCount adj job q) (unlimitedCarry adj job q).2 tail).2) := by
  induction q generalizing w job with
  | nil => simp [unlimitedCarry, replacementCount]
  | cons x xs ih =>
    by_cases ha : adj job x = true
    · have hc : replacementCount adj x xs + 1 ≤ w := by simpa [replacementCount, ha] using hw
      have hz : w ≠ 0 := by omega
      have he : w - 1 - replacementCount adj x xs = w - (replacementCount adj x xs + 1) := by omega
      simp only [List.cons_append, carry, hz, if_false, ha, if_true, unlimitedCarry,
        replacementCount, ih (w - 1) x (by omega), he]
    · have hc : replacementCount adj job xs ≤ w := by simpa [replacementCount, ha] using hw
      by_cases hz : w = 0
      · subst w
        have hh := carry_eq_unlimited_of_count adj xs 0 job hc
        rw [carry_zero] at hh
        simp [carry_zero, unlimitedCarry, replacementCount, ha, ← hh]
      · simp [carry, unlimitedCarry, replacementCount, ha, hz, ih w job hc]

end OddCycle
