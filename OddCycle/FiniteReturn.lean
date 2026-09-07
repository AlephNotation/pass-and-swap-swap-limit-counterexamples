import OddCycle.FiniteMarkov
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! First-return probabilities for a finite stochastic matrix. -/

namespace OddCycle.FiniteMarkov

open Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] (P : FiniteMarkov S)

/-- Probability of avoiding `target` at times 0 through n, starting at i.
The successor equation is the finite law of total probability. -/
def avoid (target : S) : Nat → S → ℝ
  | 0, i => if i = target then 0 else 1
  | n + 1, i => if i = target then 0 else P.expect (avoid target n) i

theorem avoid_target (target : S) (n : Nat) : P.avoid target n target = 0 := by
  cases n <;> simp [avoid]

theorem avoid_nonneg (target : S) (n : Nat) (i : S) : 0 ≤ P.avoid target n i := by
  induction n generalizing i with
  | zero => simp only [avoid]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [avoid]
    split_ifs
    · exact le_rfl
    · exact P.expect_nonneg ih i

theorem avoid_le_one (target : S) (n : Nat) (i : S) : P.avoid target n i ≤ 1 := by
  induction n generalizing i with
  | zero => simp only [avoid]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [avoid]
    split_ifs
    · exact zero_le_one
    · simpa only [P.expect_const] using P.expect_mono ih i

theorem avoid_succ_le (target : S) (n : Nat) (i : S) :
    P.avoid target (n + 1) i ≤ P.avoid target n i := by
  induction n generalizing i with
  | zero =>
    by_cases hi : i = target
    · subst i; simp only [P.avoid_target]; exact le_rfl
    · simpa only [avoid, if_neg hi] using P.avoid_le_one target 1 i
  | succ n ih =>
    simp only [avoid]
    split_ifs
    · exact le_rfl
    · exact P.expect_mono ih i

theorem avoid_antitone (target : S) (i : S) : Antitone (fun n => P.avoid target n i) :=
  antitone_nat_of_succ_le (fun n => P.avoid_succ_le target n i)

noncomputable def avoidLimit (target i : S) : ℝ := ⨅ n, P.avoid target n i

theorem avoid_tendsto (target i : S) :
    Tendsto (fun n => P.avoid target n i) atTop (𝓝 (P.avoidLimit target i)) :=
  tendsto_atTop_ciInf (P.avoid_antitone target i)
    ⟨0, by rintro _ ⟨n, rfl⟩; exact P.avoid_nonneg target n i⟩

omit [DecidableEq S] in
theorem expect_tendsto {f : Nat → S → ℝ} {g : S → ℝ}
    (h : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i))) (i : S) :
    Tendsto (fun n => P.expect (f n) i) atTop (𝓝 (P.expect g i)) := by
  exact tendsto_finset_sum _ fun j _ => tendsto_const_nhds.mul (h j)

theorem avoidLimit_harmonic (target j : S) (hj : j ≠ target) :
    P.expect (P.avoidLimit target) j = P.avoidLimit target j := by
  have h := (P.avoid_tendsto target j).comp (tendsto_add_atTop_nat 1)
  have he : (fun n => P.avoid target (n + 1) j) = (fun n => P.expect (P.avoid target n) j) := by
    funext n
    simp only [avoid, if_neg hj]
  change Tendsto (fun n => P.avoid target (n + 1) j) atTop _ at h
  rw [he] at h
  exact tendsto_nhds_unique (P.expect_tendsto (P.avoid_tendsto target) j) h

theorem avoidLimit_zero (target : S) (hreach : ∀ i, P.Reachable i target) (i : S) :
    P.avoidLimit target i = 0 := by
  apply P.harmonic_boundary_zero target hreach
  · intro j
    exact le_ciInf (fun n => P.avoid_nonneg target n j)
  · simp [avoidLimit, P.avoid_target]
  · exact P.avoidLimit_harmonic target

/-- Probability of a positive-time return by step n+1: the first step is
unrestricted, and the subsequent n steps must not all avoid the target. -/
def returnBy (target : S) (n : Nat) : ℝ :=
  1 - P.expect (P.avoid target n) target

theorem returnBy_nonneg (target : S) (n : Nat) : 0 ≤ P.returnBy target n := by
  apply sub_nonneg.mpr
  simpa only [P.expect_const] using P.expect_mono (P.avoid_le_one target n) target

theorem returnBy_le_one (target : S) (n : Nat) : P.returnBy target n ≤ 1 :=
  sub_le_self _ (P.expect_nonneg (P.avoid_nonneg target n) target)

/-- In a finite communicating chain, the probability of returning by time
n tends to one. No recurrence theorem is assumed. -/
theorem returnBy_tendsto_one (target : S) (hreach : ∀ i, P.Reachable i target) :
    Tendsto (P.returnBy target) atTop (𝓝 1) := by
  have h : ∀ i, Tendsto (fun n => P.avoid target n i) atTop (𝓝 0) := by
    intro i
    simpa only [P.avoidLimit_zero target hreach] using P.avoid_tendsto target i
  have he := (tendsto_const_nhds (x := (1 : ℝ))).sub (P.expect_tendsto h target)
  simpa only [P.expect_const, sub_zero] using he

end OddCycle.FiniteMarkov
