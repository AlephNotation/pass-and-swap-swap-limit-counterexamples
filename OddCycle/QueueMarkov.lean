import OddCycle.UniformObstruction
import OddCycle.GeneralCommunication
import OddCycle.FiniteReturn
import OddCycle.StationaryExistence
import Mathlib.Data.Fintype.List

/-! The embedded transition matrix of the limited queue on the balanced region. -/

namespace OddCycle

abbrev BalancedState (w : Nat) := {s : State // s ∈ balancedStates w}

theorem balancedState_sum {w : Nat} (hw : 2 ≤ w) (f : State → ℝ) :
    ∑ s : BalancedState w, f s.val = ((balancedStates w).map f).sum := by
  rw [← Finset.sum_subtype (balancedStates w).toFinset (fun _ => List.mem_toFinset) f]
  exact List.sum_toFinset f (balancedStates_nodup hw)

theorem balancedState_closed {w : Nat} (hw : 2 ≤ w) (s : BalancedState w)
    {e : Event} (he : e ∈ events (cycleAdjacent (2 * w + 1)) w s.val) : e.1 ∈ balancedStates w := by
  have hs := (mem_balancedStates_iff hw _).mp s.property
  exact (mem_balancedStates_iff hw _).mpr (balanced_events_closed hw hs.1 hs.2 he)

noncomputable def queueIncomingRate (w : Nat) (theta : ℝ) (s t : BalancedState w) : ℝ :=
  ((events (cycleAdjacent (2 * w + 1)) w s.val).map
    (fun e => if e.1 = t.val then spikeRate theta e.2 else 0)).sum

theorem queueIncomingRate_nonneg {w : Nat} {theta : ℝ} (ht : 0 < theta) (s t : BalancedState w) :
    0 ≤ queueIncomingRate w theta s t := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact (spikeRate_pos ht _).le
  · exact le_rfl

theorem balancedState_sum_event {w : Nat} (e : Event) (he : e.1 ∈ balancedStates w) (a : ℝ) :
    (∑ t : BalancedState w, if e.1 = t.val then a else 0) = a := by
  rw [Finset.sum_eq_single (⟨e.1, he⟩ : BalancedState w)]
  · simp
  · intro t _ ht
    exact if_neg (fun h => ht (Subtype.ext h.symm))
  · simp

theorem queueIncomingRate_sum {w : Nat} (hw : 2 ≤ w) (theta : ℝ) (s : BalancedState w) :
    ∑ t, queueIncomingRate w theta s t = theta + (2 * w : Nat) := by
  have he : ∀ es : List Event, (∀ e ∈ es, e.1 ∈ balancedStates w) →
      (∑ t : BalancedState w, (es.map (fun e => if e.1 = t.val then spikeRate theta e.2 else 0)).sum) =
        (es.map (fun e => spikeRate theta e.2)).sum := by
    intro es
    induction es with
    | nil => intro _; simp
    | cons e es ih =>
      intro h
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [balancedState_sum_event e (h e (List.mem_cons_self)), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
  unfold queueIncomingRate
  rw [he _ (fun e he => balancedState_closed hw s he)]
  exact spike_total_event_rate ((mem_balancedStates_iff hw _).mp s.property).1 theta w

/-- Every event has its initiating job's rate, and all positions together
have the same total rate theta+2w. This is the actual embedded jump matrix. -/
noncomputable def queueMarkov {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta) :
    FiniteMarkov (BalancedState w) where
  prob s t := queueIncomingRate w theta s t / (theta + (2 * w : Nat))
  nonneg s t := div_nonneg (queueIncomingRate_nonneg ht s t)
    (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg _)).le
  sum_one s := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, queueIncomingRate_sum hw]
    exact mul_inv_cancel₀ (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg _)).ne'

theorem queueMarkov_step {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta)
    (s t : BalancedState w) (hstep : EventStep (cycleAdjacent (2 * w + 1)) w s.val t.val) :
    0 < (queueMarkov hw ht).prob s t := by
  obtain ⟨i, hi⟩ := EventStep.iff_mem.mp hstep
  apply div_pos _ (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg _))
  have hm : spikeRate theta i ∈ (events (cycleAdjacent (2 * w + 1)) w s.val).map
      (fun e => if e.1 = t.val then spikeRate theta e.2 else 0) := by
    exact List.mem_map.mpr ⟨(t.val, i), hi, by simp⟩
  apply lt_of_lt_of_le (spikeRate_pos ht i) (List.single_le_sum _ _ hm)
  intro x hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact (spikeRate_pos ht _).le
  · exact le_rfl

theorem queueMarkov_irreducible {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta) :
    (queueMarkov hw ht).Irreducible := by
  intro s t
  have hs := (mem_balancedStates_iff hw _).mp s.property
  have htgt := (mem_balancedStates_iff hw _).mp t.property
  have hr := balanced_communication hw hs.1 hs.2 htgt.1 htgt.2
  have liftPath : ∀ {u : State}, EventReachable (cycleAdjacent (2 * w + 1)) w s.val u →
      ∀ hu : u ∈ balancedStates w, (queueMarkov hw ht).Reachable s ⟨u, hu⟩ := by
    intro u path
    induction path with
    | refl => intro _; exact .refl
    | @tail u v path step ih =>
      intro hv
      have hu := (mem_balancedStates_iff hw _).mpr (balanced_reachable_closed hw hs.1 hs.2 path)
      exact (ih hu).tail (queueMarkov_step hw ht ⟨u, hu⟩ ⟨v, hv⟩ step)
  exact liftPath hr t.property

theorem queue_returnBy_tendsto_one {w : Nat} (hw : 2 ≤ w) {theta : ℝ} (ht : 0 < theta)
    (s : BalancedState w) : Filter.Tendsto ((queueMarkov hw ht).returnBy s) Filter.atTop (nhds 1) :=
  (queueMarkov hw ht).returnBy_tendsto_one s (fun i => queueMarkov_irreducible hw ht i s)

end OddCycle
