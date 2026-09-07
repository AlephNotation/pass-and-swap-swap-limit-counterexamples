import OddCycle.BalancedMoves
import OddCycle.GeneralClosure

/-! The balanced event graph is strongly connected for every w ≥ 2.
This is the communication assertion used when all position rates are positive;
no recurrence or continuous-time Markov-chain theorem is assumed. -/

namespace OddCycle

/-- Conjugating the branch toggle by queue exchange and toggling once more
moves the source one vertex forward while retaining the branch direction. -/
theorem branch_shift_reachable {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) :
    EventReachable (cycleAdjacent (2 * w + 1)) w (branchState w source true)
      (branchState w ((source + 1) % (2 * w + 1)) true) := by
  have hn : 0 < 2 * w + 1 := by omega
  have hk : w + 1 < 2 * w + 1 := by omega
  let sink := cycleLabel (2 * w + 1) source true (w + 1)
  have hsink : sink < 2 * w + 1 := cycleLabel_lt hn true
  have hreturn : cycleLabel (2 * w + 1) sink false (w + 1) = source := by
    apply eq_of_zmod_eq (cycleLabel_lt hn false) hs
    rw [cast_cycleLabel hk false]
    change (cycleLabel (2 * w + 1) source true (w + 1) : ZMod (2 * w + 1)) + _ = _
    rw [cast_cycleLabel hk true]
    simp
    ring
  have hadvance : cycleLabel (2 * w + 1) sink true (w + 1) = (source + 1) % (2 * w + 1) := by
    apply eq_of_zmod_eq (cycleLabel_lt hn true) (Nat.mod_lt _ hn)
    rw [cast_cycleLabel hk true]
    change (cycleLabel (2 * w + 1) source true (w + 1) : ZMod (2 * w + 1)) + _ = _
    rw [cast_cycleLabel hk true]
    simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_one]
    calc
      (source : ZMod (2 * w + 1)) + ((w : ZMod (2 * w + 1)) + 1) + (w + 1) =
          (source + 1) + ((2 * w + 1 : Nat) : ZMod (2 * w + 1)) := by push_cast; ring
      _ = source + 1 := by simp
  have h := branch_reachable_reverse hw hsink hsink false true (branch_toggle_reachable hw hsink false)
  simp only [Bool.not_false, Bool.not_true, hreturn, hadvance] at h
  exact h.trans (branch_toggle_reachable hw (Nat.mod_lt _ hn) false)

theorem branch_advance_reachable {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (steps : Nat) :
    EventReachable (cycleAdjacent (2 * w + 1)) w (branchState w source true)
      (branchState w ((source + steps) % (2 * w + 1)) true) := by
  induction steps with
  | zero => simpa [Nat.mod_eq_of_lt hs] using
      (Relation.ReflTransGen.refl : EventReachable (cycleAdjacent (2 * w + 1)) w
        (branchState w source true) (branchState w source true))
  | succ steps ih =>
    have hh := ih.trans (branch_shift_reachable hw (Nat.mod_lt _ (show 0 < 2 * w + 1 by omega)))
    simpa only [Nat.mod_add_mod, Nat.add_assoc] using hh

theorem branch_states_communicate {w source target : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (ht : target < 2 * w + 1) (forward backward : Bool) :
    EventReachable (cycleAdjacent (2 * w + 1)) w
      (branchState w source forward) (branchState w target backward) := by
  have hstart : EventReachable (cycleAdjacent (2 * w + 1)) w
      (branchState w source forward) (branchState w source true) := by
    cases forward
    · exact branch_toggle_reachable hw hs false
    · exact .refl
  have hend : EventReachable (cycleAdjacent (2 * w + 1)) w
      (branchState w target true) (branchState w target backward) := by
    cases backward
    · exact branch_toggle_reachable hw ht true
    · exact .refl
  have hmiddle := branch_advance_reachable hw hs (unrotate (2 * w + 1) source target)
  change EventReachable _ _ _ (branchState w (rotate (2 * w + 1) source
    (unrotate (2 * w + 1) source target)) true) at hmiddle
  rw [rotate_unrotate hs ht] at hmiddle
  exact hstart.trans (hmiddle.trans hend)

/-- Manuscript Lemma 4: any two valid balanced configurations are connected
by actual queue-position completions, for every w ≥ 2. -/
theorem balanced_communication {w : Nat} (hw : 2 ≤ w) {s t : State}
    (hs : Valid (2 * w + 1) s) (hbs : balanced w s = true)
    (ht : Valid (2 * w + 1) t) (hbt : balanced w t = true) :
    EventReachable (cycleAdjacent (2 * w + 1)) w s t := by
  simp only [balanced, List.any_eq_true, beq_iff_eq] at hbs hbt
  obtain ⟨source, hsource, forward, _, hos⟩ := hbs
  obtain ⟨target, htarget, backward, _, hot⟩ := hbt
  have hsource := List.mem_range.mp hsource
  have htarget := List.mem_range.mp htarget
  exact (reachable_of_orientation_eq hs (branchState_valid hw hsource forward) hos).trans
    ((branch_states_communicate hw hsource htarget forward backward).trans
      (reachable_of_orientation_eq (branchState_valid hw htarget backward) ht hot.symm))

/-- Every intermediate state of a path from the balanced region stays in it. -/
theorem balanced_reachable_closed {w : Nat} (hw : 2 ≤ w) {s t : State}
    (hs : Valid (2 * w + 1) s) (hb : balanced w s = true)
    (h : EventReachable (cycleAdjacent (2 * w + 1)) w s t) :
    Valid (2 * w + 1) t ∧ balanced w t = true := by
  induction h with
  | refl => exact ⟨hs, hb⟩
  | tail _ hstep ih =>
    obtain ⟨_, _, _, htr⟩ := hstep
    exact ⟨transition_valid ih.1 htr, balanced_transition hw ih.1 ih.2 htr⟩

/-- Lemma 4 with the rate hypothesis explicit. Rates can depend arbitrarily
on the full configuration, queue, and occupied position. -/
theorem balanced_positive_rate_communication {R : Type*} [Zero R] [LT R]
    {w : Nat} (hw : 2 ≤ w) (rate : State → Bool → Nat → R)
    (hr : ∀ s, Valid (2 * w + 1) s → balanced w s = true →
      ∀ second pos, pos < (if second then s.2 else s.1).length → 0 < rate s second pos)
    {s t : State} (hs : Valid (2 * w + 1) s) (hbs : balanced w s = true)
    (ht : Valid (2 * w + 1) t) (hbt : balanced w t = true) :
    Relation.ReflTransGen (PositiveEventStep (cycleAdjacent (2 * w + 1)) w rate) s t := by
  have h := balanced_communication hw hs hbs ht hbt
  induction h with
  | refl => exact .refl
  | tail hpath hstep ih =>
    obtain ⟨second, pos, initiating, htr⟩ := hstep
    have hv := balanced_reachable_closed hw hs hbs hpath
    exact (ih hv.1 hv.2).tail
      ⟨second, pos, initiating, htr, hr _ hv.1 hv.2 second pos (transition_pos_lt htr)⟩

end OddCycle
