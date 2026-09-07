import OddCycle.TimedJumpLaw

/-! Hitting a closed set is permanent absorption on the actual timed paths. -/

namespace OddCycle.FiniteMarkov

open MeasureTheory Filter
open scoped NNReal Topology

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable (P : FiniteMarkov S) (rate : S → ℝ) (positive : ∀ s, 0 < rate s)

theorem continuous_eventual (s : S) (A : S → Prop) [DecidablePred A]
    (h : Tendsto (fun m => P.avoidSet A m s) atTop (𝓝 0))
    (closed : ∀ i j, A i → 0 < P.prob i j → A j) :
    ∀ᵐ ω ∂P.timedLaw s, ∃ t : ℝ≥0, ∀ u : ℝ≥0, t ≤ u → A (timedState rate positive ω u) := by
  have hit := (mem_ae_iff_prob_eq_one (continuousHit_measurable rate positive A)).mpr
    (P.continuous_absorption rate positive s A h)
  filter_upwards [hit, P.timedLaw_ae_steps s] with ω hω hsteps
  obtain ⟨n, hn⟩ := (ClockedPath.visits_iff rate positive ω.1 ω.2 A).mp hω
  have hall : ∀ m, n ≤ m → A (ω.1 m) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hn
    | succ m hm ih => exact closed _ _ ih (hsteps m)
  refine ⟨⟨eventTime rate ω n, ClockedPath.arrival_nonneg rate positive ω.1 ω.2 n⟩, ?_⟩
  intro u hu
  apply hall
  have hh := ClockedPath.index_upper rate positive ω.1 ω.2 u
  have hm := ClockedPath.arrival_strictMono rate positive ω.1 ω.2
  have hlt := hm.lt_iff_lt.mp ((show ClockedPath.arrival rate ω.1 ω.2 n ≤ u from hu).trans_lt hh)
  omega

theorem continuous_eventually_one_class (s : S) :
    ∀ᵐ ω ∂P.timedLaw s, ∃ i : S, ∃ t : ℝ≥0,
      ReachabilityQuotient.Terminal (fun a b => 0 < P.prob a b) i ∧
      ∀ u : ℝ≥0, t ≤ u → P.Reachable i (timedState rate positive ω u) ∧
        P.Reachable (timedState rate positive ω u) i := by
  classical
  let A := ReachabilityQuotient.Terminal (fun a b => 0 < P.prob a b)
  have hit := (mem_ae_iff_prob_eq_one (continuousHit_measurable rate positive A)).mpr
    (P.continuous_absorption rate positive s A (P.avoid_terminal_tendsto_zero s))
  filter_upwards [hit, P.timedLaw_ae_steps s] with ω hω hsteps
  obtain ⟨n, hn⟩ := (ClockedPath.visits_iff rate positive ω.1 ω.2 A).mp hω
  have hall : ∀ m, n ≤ m → P.Reachable (ω.1 n) (ω.1 m) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact .refl
    | succ m hm ih => exact ih.tail (hsteps m)
  refine ⟨ω.1 n, ⟨eventTime rate ω n, ClockedPath.arrival_nonneg rate positive ω.1 ω.2 n⟩, hn, ?_⟩
  intro u hu
  have hindex : n ≤ ClockedPath.index rate positive ω.1 ω.2 u := by
    have hh := ClockedPath.index_upper rate positive ω.1 ω.2 u
    have hm := ClockedPath.arrival_strictMono rate positive ω.1 ω.2
    have hlt := hm.lt_iff_lt.mp ((show ClockedPath.arrival rate ω.1 ω.2 n ≤ u from hu).trans_lt hh)
    omega
  exact ⟨hall _ hindex, hn _ (hall _ hindex)⟩

end OddCycle.FiniteMarkov
