import OddCycle.TerminalRecurrence

/-! A finite state's positive-time return probability tends to one exactly
when its communicating component is terminal. -/

namespace OddCycle.FiniteMarkov

open Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] (P : FiniteMarkov S)

theorem avoid_eq_one_of_unreachable (target : S) {i : S}
    (hi : ¬ P.Reachable i target) (n : Nat) : P.avoid target n i = 1 := by
  induction n generalizing i with
  | zero => simp only [avoid, if_neg (show i ≠ target from fun h => hi (h ▸ .refl))]
  | succ n ih =>
    rw [avoid, if_neg (show i ≠ target from fun h => hi (h ▸ .refl))]
    unfold expect
    calc
      _ = ∑ j, P.prob i j := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hp : 0 < P.prob i j
        · rw [ih (fun hj => hi ((show P.Reachable i j from .single hp).trans hj)), mul_one]
        · rw [le_antisymm (le_of_not_gt hp) (P.nonneg i j), zero_mul]
      _ = 1 := P.sum_one i

theorem avoidLimit_nonneg (target i : S) : 0 ≤ P.avoidLimit target i :=
  le_ciInf (fun n => P.avoid_nonneg target n i)

omit [DecidableEq S] in
theorem expect_zero_step {f : S → ℝ} (hf : ∀ i, 0 ≤ f i) {i j : S}
    (hz : P.expect f i = 0) (hp : 0 < P.prob i j) : f j = 0 := by
  have hh := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => mul_nonneg (P.nonneg i k) (hf k))).mp hz j (Finset.mem_univ j)
  exact (mul_eq_zero.mp hh).resolve_left hp.ne'

theorem terminal_of_returnBy_tendsto_one (target : S)
    (h : Tendsto (P.returnBy target) atTop (𝓝 1)) :
    ReachabilityQuotient.Terminal (fun a b => 0 < P.prob a b) target := by
  have hl := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (P.expect_tendsto (P.avoid_tendsto target) target)
  have hz : P.expect (P.avoidLimit target) target = 0 := by
    have he := tendsto_nhds_unique h hl
    linarith
  have hzero : ∀ i, P.Reachable target i → P.avoidLimit target i = 0 := by
    intro i hr
    induction hr with
    | refl => simp [avoidLimit, P.avoid_target]
    | @tail i j hr hp ih =>
      apply P.expect_zero_step (P.avoidLimit_nonneg target) _ hp
      by_cases hi : i = target
      · simpa only [hi] using hz
      · rw [P.avoidLimit_harmonic target i hi, ih]
  intro i hi
  by_contra hn
  have he : P.avoidLimit target i = 1 := by
    unfold avoidLimit
    simp only [P.avoid_eq_one_of_unreachable target hn, ciInf_const]
  have hh := hzero i hi
  linarith

theorem returnBy_tendsto_one_iff_terminal (target : S) :
    Tendsto (P.returnBy target) atTop (𝓝 1) ↔
      ReachabilityQuotient.Terminal (fun a b => 0 < P.prob a b) target :=
  ⟨P.terminal_of_returnBy_tendsto_one target, P.terminal_returnBy_tendsto_one target⟩

end OddCycle.FiniteMarkov
