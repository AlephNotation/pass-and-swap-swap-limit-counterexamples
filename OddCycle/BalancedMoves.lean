import OddCycle.BalancedSymmetry
import OddCycle.WordCommunication

/-! Explicit head completions connect the two balanced orientations with a
fixed source. Queue exchange supplies the second orientation move. -/

namespace OddCycle

theorem carry_zero (adj : Nat → Nat → Bool) (job : Nat) (q : Queue) :
    carry adj 0 job q = (q, job) := by cases q <;> simp [carry]

/-- A consecutive compatible chain consumes exactly its replacement budget. -/
theorem carry_chain {adj : Nat → Nat → Bool} (f : Nat → Nat) (k count : Nat) (q : Queue)
    (h : ∀ i, k ≤ i → i < k + count → adj (f i) (f (i + 1)) = true) :
    carry adj count (f k) ((List.range' (k + 1) count).map f ++ q) =
      ((List.range' k count).map f ++ q, f (k + count)) := by
  induction count generalizing k with
  | zero => simp [carry_zero]
  | succ count ih =>
    have ha := h k (by omega) (by omega)
    have hh := ih (k + 1) (fun i hi hi' => h i (by omega) (by omega))
    simpa [List.range'_succ, carry, ha, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg (fun result : Queue × Nat => (f k :: result.1, result.2)) hh

def branchHeadState (w source : Nat) (forward : Bool) : State :=
  (((List.range w).map (cycleLabel (2 * w + 1) source forward) ++
    (List.range' (w + 1) w).reverse.map (cycleLabel (2 * w + 1) source forward)),
    [cycleLabel (2 * w + 1) source forward w])

theorem branch_head_transition {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (forward : Bool) :
    transition (cycleAdjacent (2 * w + 1)) w (branchState w source forward) false 0 =
      some (branchHeadState w source forward, cycleLabel (2 * w + 1) source forward 0) := by
  let f := cycleLabel (2 * w + 1) source forward
  have hc := carry_chain (adj := cycleAdjacent (2 * w + 1)) f 0 w
    ((List.range' (w + 1) w).reverse.map f) (by
      intro i _ hi
      apply (cycleLabel_adj_iff hs (by omega) (by omega) forward).mpr
      simp [cycleAdjacent, Nat.mod_eq_of_lt (show i + 1 < 2 * w + 1 by omega)])
  simp only [Nat.zero_add] at hc
  have hword : branchWord w source forward = f 0 ::
      ((List.range' 1 w).map f ++ (List.range' (w + 1) w).reverse.map f) := by
    rw [branchWord_eq_map_folded hw hs forward]
    simp [foldedWord, List.range_eq_range', List.range'_succ, f]
  simp [transition, branchState, hword, complete, branchHeadState, List.range_eq_range', f]
  exact ⟨by simpa [f] using congrArg Prod.fst hc,
    by simpa [f] using congrArg Prod.snd hc⟩

theorem branch_head_orientation {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (forward : Bool) :
    orientation (2 * w + 1) (branchHeadState w source forward) =
      orientation (2 * w + 1) (branchState w source (!forward)) := by
  have hn : 0 < 2 * w + 1 := by omega
  have hv := branchState_valid hw hs forward
  have htr := branch_head_transition hw hs forward
  have ht := transition_valid hv htr
  let p := cycleLabel (2 * w + 1) source forward w
  let v := cycleLabel (2 * w + 1) source forward (w + 1)
  have hmem : v ∈ (branchHeadState w source forward).1 := by
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨w + 1, ?_, rfl⟩
    simp only [List.mem_reverse, List.mem_range'_1]
    omega
  have hnot : p ∉ (branchHeadState w source forward).1 := by
    have hnd : ((branchHeadState w source forward).1 ++ [p]).Nodup := ht.placement_nodup
    exact (List.nodup_cons.mp ((List.perm_append_singleton p _).nodup_iff.mp hnd)).1
  have hbefore : (placement (branchHeadState w source forward)).idxOf v <
      (placement (branchHeadState w source forward)).idxOf p := by
    change (((branchHeadState w source forward).1) ++ [p]).idxOf v <
      (((branchHeadState w source forward).1) ++ [p]).idxOf p
    simp only [List.idxOf_append, if_pos hmem, if_neg hnot, List.idxOf_cons_self, Nat.zero_add]
    exact List.idxOf_lt_length_of_mem hmem
  have hone := branchState_flip_boundary_before hw hs forward
  change (placement (branchState w source (!forward))).idxOf v <
    (placement (branchState w source (!forward))).idxOf p at hone
  have he : EdgeEquiv (eraseEdge (cycleAdjacent (2 * w + 1)) p v)
      (placement (branchState w source forward)) (placement (branchHeadState w source forward)) := by
    apply transition_first_edgeEquiv_erase (rank := frameRank w source forward)
      (allowed := fun x => x < 2 * w + 1) (cycleAdjacent_symm (2 * w + 1))
    · intro a b ha hb hhigh hup _
      exact Or.inl (frameRank_boundary hs ha hb forward hhigh hup)
    · intro x hx
      exact hv.placement_mem.mp (List.mem_append_left _ hx)
    · exact rankOrdered_of_orientation hw hs hv forward rfl
    · exact htr
  apply orientation_eq_of_except hn (p := p) (v := v)
  · omega
  · exact iff_of_true hbefore hone
  · intro a b ha hb hab hex
    have hr : eraseEdge (cycleAdjacent (2 * w + 1)) p v a b = true := by
      simp [eraseEdge, hab]
      tauto
    exact (he.before_iff hr).symm.trans (branchState_flip_before hw hs ha hb hab forward hex)

theorem branch_toggle_reachable {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (forward : Bool) :
    EventReachable (cycleAdjacent (2 * w + 1)) w (branchState w source forward)
      (branchState w source (!forward)) := by
  have htr := branch_head_transition hw hs forward
  exact (Relation.ReflTransGen.single ⟨false, 0, _, htr⟩).trans
    (reachable_of_orientation_eq (transition_valid (branchState_valid hw hs forward) htr)
      (branchState_valid hw hs (!forward)) (branch_head_orientation hw hs forward))

theorem branch_reachable_reverse {w source target : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (ht : target < 2 * w + 1) (forward backward : Bool)
    (h : EventReachable (cycleAdjacent (2 * w + 1)) w
      (branchState w source forward) (branchState w target backward)) :
    EventReachable (cycleAdjacent (2 * w + 1)) w
      (branchState w (cycleLabel (2 * w + 1) source forward (w + 1)) (!forward))
      (branchState w (cycleLabel (2 * w + 1) target backward (w + 1)) (!backward)) := by
  have hn : 0 < 2 * w + 1 := by omega
  exact (reachable_of_orientation_eq (branchState_valid hw (cycleLabel_lt hn forward) (!forward))
    (branchState_valid hw hs forward).exchange (branchState_reverse_orientation hw hs forward).symm).trans
      (h.exchange.trans (reachable_of_orientation_eq (branchState_valid hw ht backward).exchange
        (branchState_valid hw (cycleLabel_lt hn backward) (!backward))
        (branchState_reverse_orientation hw ht backward)))

end OddCycle
