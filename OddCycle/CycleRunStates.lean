import OddCycle.CircularWords
import OddCycle.ExceptionalCycleArithmetic

/-! Circular runs extracted from the original queue orientation. These
predicates describe the proposed classification; no recurrence equivalence
is built into their definitions. -/

namespace OddCycle

theorem orientation_length (n : Nat) (s : State) : (orientation n s).length = n := by
  simp [orientation]

theorem orientation_nonconstant {n : Nat} {s : State} (hn : 2 ≤ n) (hs : Valid n s) :
    CircularWord.Nonconstant (orientation n s) := by
  have hp := hs.placement_perm
  have hlen : (placement s).length = n := by simpa using hp.length_eq
  cases he : placement s with
  | nil => simp [he] at hlen; omega
  | cons a q =>
    have ha : a < n := hs.placement_mem.mp (by simp [he])
    let prev := if a = 0 then n - 1 else a - 1
    have hprev : prev < n := by dsimp [prev]; split_ifs <;> omega
    have hsuccprev : (prev + 1) % n = a := by
      dsimp [prev]
      split_ifs with hz
      · subst a
        rw [show n - 1 + 1 = n by omega]
        simp
      · rw [show a - 1 + 1 = a by omega, Nat.mod_eq_of_lt ha]
    have hnext : (a + 1) % n ≠ a := by
      by_cases htop : a + 1 = n
      · rw [htop, Nat.mod_self]; omega
      · rw [Nat.mod_eq_of_lt (show a + 1 < n by omega)]; omega
    have ht : true ∈ orientation n s := by
      apply List.mem_map.mpr
      refine ⟨a, List.mem_range.mpr ha, ?_⟩
      simp [he, Ne.symm hnext]
    have hf : false ∈ orientation n s := by
      apply List.mem_map.mpr
      refine ⟨prev, List.mem_range.mpr hprev, ?_⟩
      simp [he, hsuccprev]
    exact ⟨true, ht, false, hf, by decide⟩

def cycleRuns (n : Nat) (s : State) : List Nat :=
  CircularWord.circularRuns (orientation n s)

theorem cycleRuns_sum (n : Nat) (s : State) : (cycleRuns n s).sum = n := by
  simp [cycleRuns, CircularWord.circularRuns_sum, orientation_length]

theorem cycleRuns_positive (n : Nat) (s : State) : ∀ a ∈ cycleRuns n s, 0 < a :=
  CircularWord.circularRuns_positive _

theorem cycleRuns_even {n : Nat} {s : State} (hn : 2 ≤ n) (hs : Valid n s) :
    Even (cycleRuns n s).length :=
  CircularWord.circularRuns_even (orientation_nonconstant hn hs)

def ShortRuns (n w : Nat) (s : State) : Prop := CircularRun.Short w (cycleRuns n s)

def ExceptionalRuns (n w : Nat) (s : State) : Prop := CircularRun.Exceptional w (cycleRuns n s)

theorem exceptionalRuns_cycle_length {n w : Nat} {s : State} (hn : 2 ≤ n)
    (hs : Valid n s) (he : ExceptionalRuns n w s) : ∃ k, 1 ≤ k ∧ n = 2 * k * w + 1 :=
  CircularRun.exceptional_cycle_length he (cycleRuns_sum n s) (cycleRuns_even hn hs)

theorem even_cycle_not_exceptional {n w : Nat} {s : State} (hn : 2 ≤ n)
    (hs : Valid n s) (heven : Even n) : ¬ ExceptionalRuns n w s := by
  intro he
  obtain ⟨k, _, hk⟩ := exceptionalRuns_cycle_length hn hs he
  obtain ⟨m, hm⟩ := heven
  have hk' : n = 2 * (k * w) + 1 := by rw [hk]; ring
  omega

end OddCycle
