import OddCycle.CompletionKernel
import OddCycle.HiddenCanonicalDefect

/-! The queue-length generator identity for the repository's actual unit-rate
completion kernel, retaining all position-event multiplicities. -/

noncomputable section

namespace OddCycle

open Finset

def unitPositions (n : Nat) : PositivePositionAllocation n :=
  (unitAllocation n).positions (unitAllocation n)

theorem unitPositions_rate {n : Nat} (s : State) (side : Bool) (p : Nat)
    (hp : p < (if side then s.2 else s.1).length) : (unitPositions n).rate s side p = 1 := by
  cases side <;> exact unit_increment _ _ hp

theorem unitPositions_total {n : Nat} (s : CycleState n) : (unitPositions n).total s = n := by
  have hl := s.property.length_eq
  simp only [List.length_append, List.length_range] at hl
  have hh : ((positions s.val).map (fun p => (unitPositions n).rate s.val p.1 p.2)) =
      (positions s.val).map (fun _ => (1 : ℝ)) := by
    apply List.map_congr_left
    intro p hp
    exact unitPositions_rate _ _ _ ((mem_positions _ _ _).mp hp)
  unfold PositivePositionAllocation.total
  rw [hh]
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one, positions,
    List.length_append, List.length_map, List.length_range, hl]

private theorem sum_map_swap {I A : Type*} [Fintype I] (xs : List A) (g : I → A → ℝ) :
    (∑ i, (xs.map (g i)).sum) = (xs.map (fun x => ∑ i, g i x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem PositivePositionAllocation.incoming_expect {n : Nat} (a : PositivePositionAllocation n)
    (w : Nat) (s : CycleState n) (g : State → ℝ) :
    (∑ t, a.incoming w s t * g t.val) =
      ((positions s.val).map (fun p => a.rate s.val p.1 p.2 *
        ((transition (cycleAdjacent n) w s.val p.1 p.2).map (fun e => g e.1)).getD 0)).sum := by
  classical
  unfold PositivePositionAllocation.incoming
  simp only [← List.sum_map_mul_right]
  rw [sum_map_swap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  obtain ⟨⟨t, i⟩, he⟩ := positions_are_events (cycleAdjacent n) w s.val hp
  let v : CycleState n := ⟨t, transition_valid s.property he⟩
  rw [Finset.sum_eq_single v]
  · simp only [he, Option.map_some, Option.getD_some]
    rw [if_pos ⟨i, rfl⟩]
  · intro u _ hu
    rw [if_neg, zero_mul]
    rintro ⟨j, hj⟩
    have hh := (Prod.mk.inj (Option.some.inj (he.symm.trans hj))).1
    exact hu (Subtype.ext hh.symm)
  · simp

theorem unitKernel_length_generator {n : Nat} (hn : 0 < n) (w : Nat) (s : CycleState n) (f : Nat → ℝ) :
    (n : ℝ) * (((unitPositions n).kernel hn w).expect (fun t => f t.val.1.length) s - f s.val.1.length) =
      lengthGenerator (cycleAdjacent n) w (fun _ => 1) (fun _ => 1) s.val f := by
  have hpos : ∀ p ∈ positions s.val,
      (unitPositions n).rate s.val p.1 p.2 = 1 :=
    fun p hp => unitPositions_rate _ _ _ ((mem_positions _ _ _).mp hp)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hexp : (n : ℝ) * (((unitPositions n).kernel hn w).expect (fun t => f t.val.1.length) s) =
      ∑ t, (unitPositions n).incoming w s t * f t.val.1.length := by
    unfold FiniteMarkov.expect PositivePositionAllocation.kernel
    simp only [unitPositions_total, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    field_simp
  rw [mul_sub, hexp, PositivePositionAllocation.incoming_expect (unitPositions n) w s
    (fun t => f t.1.length)]
  have hd : ((positions s.val).map (fun p => (unitPositions n).rate s.val p.1 p.2 *
        ((transition (cycleAdjacent n) w s.val p.1 p.2).map (fun e => f e.1.1.length)).getD 0)).sum -
      n * f s.val.1.length =
      ((positions s.val).map (fun p => lengthPositionDifference (cycleAdjacent n) w s.val p.1 p.2 f)).sum := by
    have hlen : (positions s.val).length = n := by
      have hl := s.property.length_eq
      simpa only [positions, List.length_append, List.length_map, List.length_range] using hl
    have hc : (n : ℝ) * f s.val.1.length =
        ((positions s.val).map (fun _ => f s.val.1.length)).sum := by
      simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, hlen]
    rw [hc, ← sum_map_sub]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    obtain ⟨e, he⟩ := positions_are_events (cycleAdjacent n) w s.val hp
    simp only [hpos p hp, one_mul, he, Option.map_some, Option.getD_some, lengthPositionDifference]
  rw [hd]
  simp only [positions, List.map_append, List.map_map, Function.comp_def, List.sum_append,
    lengthGenerator, one_mul]

end OddCycle
