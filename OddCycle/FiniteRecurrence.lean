import OddCycle.FiniteReturn
import OddCycle.StationaryExistence

/-! A finite chain contains a recurrent state, without irreducibility. -/

namespace OddCycle.FiniteMarkov

open Filter Topology

variable {S : Type*} [Fintype S] (P : FiniteMarkov S)

theorem stationary_expect {v : S → ℝ} (hv : P.StationaryVector v) (f : S → ℝ) :
    ∑ i, v i * P.expect f i = ∑ i, v i * f i := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul]
  change (∑ j, P.advance v j * f j) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [hv j]

variable [DecidableEq S]

theorem stationary_returnBy_tendsto_one {v : S → ℝ} (hv : P.StationaryVector v)
    (target : S) (ht : 0 < v target) : Tendsto (P.returnBy target) atTop (𝓝 1) := by
  let f := P.avoidLimit target
  have hz : f target = 0 := by simp [f, avoidLimit, P.avoid_target]
  have he : ∑ i, v i * (P.expect f i - f i) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, P.stationary_expect hv f, sub_self]
  rw [Finset.sum_eq_single target] at he
  · rw [hz, sub_zero] at he
    have hzero := (mul_eq_zero.mp he).resolve_left ht.ne'
    change P.expect (P.avoidLimit target) target = 0 at hzero
    have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub (P.expect_tendsto (P.avoid_tendsto target) target)
    simpa only [hzero, sub_zero] using hlim
  · intro i _ hi
    rw [P.avoidLimit_harmonic target i hi, sub_self, mul_zero]
  · simp

theorem recurrent_state_exists [Nonempty S] :
    ∃ target : S, Tendsto (P.returnBy target) atTop (𝓝 1) := by
  obtain ⟨v, hv, hs⟩ := P.stationary_exists
  have hex : ∃ i, 0 < v i := by
    by_contra h
    have hz : ∀ i, v i = 0 := fun i =>
      le_antisymm (le_of_not_gt (fun hi => h ⟨i, hi⟩)) (hv.1 i)
    have he := hv.2
    simp only [hz, Finset.sum_const_zero] at he
    exact zero_ne_one he
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, P.stationary_returnBy_tendsto_one hs i hi⟩

end OddCycle.FiniteMarkov
