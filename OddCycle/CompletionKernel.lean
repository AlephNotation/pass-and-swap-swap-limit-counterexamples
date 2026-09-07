import OddCycle.CycleRecurrenceClassification
import OddCycle.OIGenerator

/-! The completion-epoch stochastic kernel built from arbitrary positive
position rates, including multiplicities of events with the same destination. -/

namespace OddCycle

structure PositivePositionAllocation (n : Nat) where
  rate : State → Bool → Nat → ℝ
  positive : ∀ s, Valid n s → ∀ side p, p < (if side then s.2 else s.1).length → 0 < rate s side p

namespace PositivePositionAllocation

variable {n : Nat} (a : PositivePositionAllocation n)

noncomputable def total (s : CycleState n) : ℝ :=
  ((positions s.val).map (fun p => a.rate s.val p.1 p.2)).sum

noncomputable def incoming (w : Nat) (s t : CycleState n) : ℝ := by
  classical
  exact ((positions s.val).map (fun p =>
    if ∃ init, transition (cycleAdjacent n) w s.val p.1 p.2 = some (t.val, init)
    then a.rate s.val p.1 p.2 else 0)).sum

theorem total_pos (hn : 0 < n) (s : CycleState n) : 0 < a.total s := by
  apply List.sum_pos
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact a.positive s.val s.property _ _ ((mem_positions _ _ _).mp hp)
  · have hlen := s.property.length_eq
    simp only [List.length_append, List.length_range] at hlen
    intro he
    have hh := congrArg List.length he
    simp only [List.length_map, positions, List.length_append, List.length_range, List.length_nil] at hh
    omega

theorem incoming_nonneg (w : Nat) (s t : CycleState n) : 0 ≤ a.incoming w s t := by
  classical
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact (a.positive s.val s.property _ _ ((mem_positions _ _ _).mp hp)).le
  · exact le_rfl

theorem incoming_pos_iff (w : Nat) (s t : CycleState n) :
    0 < a.incoming w s t ↔ CycleState.Step n w s t := by
  classical
  constructor
  · intro hp
    by_contra he
    have hzero : a.incoming w s t = 0 := by
      unfold incoming
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
      exact if_neg (fun ⟨i, hi⟩ => he ⟨p.1, p.2, i, hi⟩)
    rw [hzero] at hp
    exact lt_irrefl 0 hp
  · rintro ⟨side, p, init, he⟩
    have hp := transition_pos_lt he
    have hm : a.rate s.val side p ∈ ((positions s.val).map (fun q =>
        if ∃ i, transition (cycleAdjacent n) w s.val q.1 q.2 = some (t.val, i)
        then a.rate s.val q.1 q.2 else 0)) := by
      exact List.mem_map.mpr ⟨(side, p), (mem_positions _ _ _).mpr hp, if_pos ⟨init, he⟩⟩
    apply lt_of_lt_of_le (a.positive s.val s.property side p hp) (List.single_le_sum _ _ hm)
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    split_ifs
    · exact (a.positive s.val s.property _ _ ((mem_positions _ _ _).mp hq)).le
    · exact le_rfl

theorem incoming_sum (w : Nat) (s : CycleState n) : ∑ t, a.incoming w s t = a.total s := by
  classical
  have swap (ps : List (Bool × Nat)) :
      (∑ t : CycleState n, (ps.map (fun p => if ∃ init,
        transition (cycleAdjacent n) w s.val p.1 p.2 = some (t.val, init) then a.rate s.val p.1 p.2 else 0)).sum) =
      (ps.map (fun p => ∑ t : CycleState n, if ∃ init,
        transition (cycleAdjacent n) w s.val p.1 p.2 = some (t.val, init) then a.rate s.val p.1 p.2 else 0)).sum := by
    induction ps with
    | nil => simp
    | cons p ps ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
  unfold incoming total
  rw [swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  obtain ⟨⟨t, i⟩, he⟩ := positions_are_events (cycleAdjacent n) w s.val hp
  let v : CycleState n := ⟨t, transition_valid s.property he⟩
  rw [Finset.sum_eq_single v]
  · exact if_pos ⟨i, he⟩
  · intro b _ hb
    apply if_neg
    rintro ⟨j, hj⟩
    have hh := (Prod.mk.inj (Option.some.inj (he.symm.trans hj))).1
    exact hb (Subtype.ext hh.symm)
  · simp

noncomputable def kernel (hn : 0 < n) (w : Nat) : FiniteMarkov (CycleState n) where
  prob s t := a.incoming w s t / a.total s
  nonneg s t := div_nonneg (a.incoming_nonneg w s t) (a.total_pos hn s).le
  sum_one s := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, a.incoming_sum]
    exact mul_inv_cancel₀ (a.total_pos hn s).ne'

theorem kernel_pos_iff (hn : 0 < n) (w : Nat) (s t : CycleState n) :
    0 < (a.kernel hn w).prob s t ↔ CycleState.Step n w s t := by
  change 0 < a.incoming w s t / a.total s ↔ _
  rw [div_pos_iff_of_pos_right (a.total_pos hn s), a.incoming_pos_iff]

theorem recurrent_iff_runs (hn : 3 ≤ n) {w : Nat} (hw : 1 ≤ w) (s : CycleState n) :
    Filter.Tendsto ((a.kernel (by omega) w).returnBy s) Filter.atTop (nhds 1) ↔
      ShortRuns n w s.val ∨ ExceptionalRuns n w s.val :=
  CycleState.recurrent_iff_runs _ (fun s t h => Or.inl ((a.kernel_pos_iff _ w s t).mp h))
    (fun s t h => (a.kernel_pos_iff _ w s t).mpr h) hn hw s

attribute [local instance] Classical.propDecidable

theorem classified_absorption (hn : 3 ≤ n) {w : Nat} (hw : 1 ≤ w) (s : CycleState n) :
    Filter.Tendsto (fun j => (a.kernel (by omega) w).avoidSet
      (fun t => ShortRuns n w t.val ∨ ExceptionalRuns n w t.val) j s) Filter.atTop (nhds 0) :=
  CycleState.classified_avoid_tendsto_zero _
    (fun s t h => Or.inl ((a.kernel_pos_iff _ w s t).mp h))
    (fun s t h => (a.kernel_pos_iff _ w s t).mpr h) hn hw s

theorem short_absorption (hn : 3 ≤ n) {w : Nat} (hw : 1 ≤ w)
    (hlength : ¬ ∃ k, 1 ≤ k ∧ n = 2 * k * w + 1) (s : CycleState n) :
    Filter.Tendsto (fun j => (a.kernel (by omega) w).avoidSet
      (fun t => ShortRuns n w t.val) j s) Filter.atTop (nhds 0) :=
  CycleState.short_avoid_tendsto_zero _
    (fun s t h => Or.inl ((a.kernel_pos_iff _ w s t).mp h))
    (fun s t h => (a.kernel_pos_iff _ w s t).mpr h) hn hw hlength s

end PositivePositionAllocation

noncomputable def PositiveOIAllocation.positions {n : Nat} (μ ν : PositiveOIAllocation n) : PositivePositionAllocation n where
  rate := oiPositionRate μ.toOICapacity ν.toOICapacity
  positive s hs side p hp := by
    cases side <;> simp only [oiPositionRate, Bool.false_eq_true, if_false, if_true] at hp ⊢
    · exact μ.positive _ hs.first_subperm _ hp
    · exact ν.positive _ hs.second_subperm _ hp

end OddCycle
