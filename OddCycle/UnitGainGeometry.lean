import OddCycle.UnitInterior
import OddCycle.EdgeBitFlips

namespace OddCycle

theorem unit_gain_valid {n w : Nat} {R : Queue} (hv : Valid n (unitPatternTarget n w R)) :
    Valid n (unitGainOccurrence n w R).source := by
  have hp := (reverseInput_perm (adj := cycleAdjacent n) (unitInitialBlock n w) 0 0).append_right (R ++ unitTargetTail w)
  have hm : (unitInitialBlock n w ++ 0 :: (R ++ unitTargetTail w)).Perm
      (0 :: (unitInitialBlock n w ++ (R ++ unitTargetTail w))) := List.perm_middle
  change (reverseInput (cycleAdjacent n) (unitInitialBlock n w) 0 0 ++ (R ++ unitTargetTail w)).Perm _
  apply (hp.trans ?_).trans hv
  simpa only [unitPatternTarget, List.append_assoc, List.singleton_append] using hm

theorem unit_gain_edge_flip {n w : Nat} (hw : 1 ≤ w) (hn : 3 * w + 2 ≤ n) (R : Queue)
    (hv : Valid n (unitPatternTarget n w R)) :
    EdgeBitFlip n (unitPatternTarget n w R) (unitGainOccurrence n w R).source 0 := by
  let A := unitInitialBlock n w
  let T := R ++ unitTargetTail w
  let s := unitPatternTarget n w R
  let g := (unitGainOccurrence n w R).source
  have hp : placement s = 0 :: (T.reverse ++ A.reverse) := by
    simp [s, unitPatternTarget, placement, A, T, List.reverse_append, List.append_assoc]
  have he : EdgeEquiv (cycleAdjacent n) (placement g) (T.reverse ++ 0 :: A.reverse) := by
    simpa only [g, unitGainOccurrence, reconstructedGain, placement, List.nil_append,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.singleton_append, List.append_assoc, A, T] using
      ((reverseInput_edgeEquiv (cycleAdjacent_symm n) A 0 0).append_right T).reverse
  have hnot : n - 1 ∉ T := by
    have hnd : (A ++ T).Nodup := by
      simpa only [unitPatternTarget, List.nil_append, List.append_assoc, A, T] using (List.nodup_cons.mp (hv.nodup_iff.mpr List.nodup_range)).2
    have ham : n - 1 ∈ A := mem_range_interval.mpr ⟨by omega, by omega⟩
    intro hh
    exact (List.nodup_append.mp hnd).2.2 _ ham _ hh rfl
  have hno : ∀ x ∈ T.reverse, eraseEdge (cycleAdjacent n) 0 1 0 x = false := by
    intro x hx
    have hxm := List.mem_reverse.mp hx
    have hxn : x < n := List.mem_range.mp (hv.second_subperm.subset (by simpa only [unitPatternTarget, List.append_assoc, A, T] using List.mem_append_right A hxm))
    by_cases hx1 : x = 1
    · simp [eraseEdge, hx1]
    · have hxn1 : x ≠ n - 1 := by intro hh; subst x; exact hnot hxm
      have ha : cycleAdjacent n 0 x = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        have hh' := (cycleAdjacent_iff (by omega : 0 < n) hxn).mp hh
        omega
      simp [eraseEdge, ha]
  have herase : EdgeEquiv (eraseEdge (cycleAdjacent n) 0 1) (placement s) (placement g) := by
    rw [hp]
    have hh := ((edgeEquiv_move (eraseEdge_symm (cycleAdjacent_symm n) 0 1) hno).append_right A.reverse)
    have hh' : EdgeEquiv (eraseEdge (cycleAdjacent n) 0 1) (0 :: (T.reverse ++ A.reverse))
        (T.reverse ++ 0 :: A.reverse) := by simpa only [List.cons_append, List.append_assoc, List.singleton_append] using hh
    exact hh'.trans (he.erase 0 1).symm
  have hz : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
  refine ⟨edgeBits_eq_of_erase (by omega) (by omega) (by simpa only [hz] using herase), ?_⟩
  have hm1 : 1 ∈ T.reverse := by
    apply List.mem_reverse.mpr
    obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp (unit_pattern_last (w := w) hw R)
    simp [T, hpre]
  have hbefore : (placement g).idxOf 1 < (placement g).idxOf 0 := by
    have hnot0 : 0 ∉ T.reverse := by
      intro hh
      have hnd := List.nodup_cons.mp (hv.nodup_iff.mpr List.nodup_range)
      exact hnd.1 (by simpa only [unitPatternTarget, List.nil_append, List.append_assoc, A, T] using List.mem_append_right A (List.mem_reverse.mp hh))
    apply (he.before_iff (a := 1) (b := 0) (by rw [cycleAdjacent_symm]; exact cycle_consecutive (by omega))).mpr
    simp only [List.idxOf_append_of_mem hm1, List.idxOf_append_of_notMem hnot0, List.idxOf_cons_self, add_zero]
    exact List.idxOf_lt_length_iff.mpr hm1
  have hgbit : edgeBit n g 0 = false := by
    apply (edgeBit_false_iff (by omega) (by omega) (unit_gain_valid hv)).mpr
    simpa only [hz] using hbefore
  have hsbit : edgeBit n s 0 = true := by
    change decide ((placement s).idxOf 0 < (placement s).idxOf ((0 + 1) % n)) = true
    rw [hp, hz]
    simp
  exact hgbit.trans (congrArg Bool.not hsbit).symm

end OddCycle
