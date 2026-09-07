import OddCycle.UnitLostPredecessors
import OddCycle.UnitInitialBlock
import OddCycle.ReconstructedGain

namespace OddCycle

def unitPatternTarget (n w : Nat) (R : Queue) : State :=
  ([0], (unitInitialBlock n w ++ R) ++ unitTargetTail w)

def unitGainOccurrence (n w : Nat) (R : Queue) : Occurrence :=
  ⟨([], reconstructedGain (cycleAdjacent n) (unitInitialBlock n w) 0 (R ++ unitTargetTail w)), true, 0,
    (unlimitedCarry (cycleAdjacent n) 0 (unitInitialBlock n w).reverse).2⟩

theorem unit_gain_complete {n w : Nat} (hw : 1 ≤ w) (hn : w < n) (R : Queue) :
    complete (cycleAdjacent n) w (unitGainOccurrence n w R).source.2 0 =
      some ((unitPatternTarget n w R).2, 0, (unitGainOccurrence n w R).initiating) := by
  simpa only [unitGainOccurrence, unitPatternTarget, List.append_assoc] using
    reconstructedGain_complete (cycleAdjacent_symm n) (unitInitialBlock n w) (R ++ unitTargetTail w) 0 w
      (unitInitialBlock_backward_count (by omega) hn)

theorem unit_gain_changed {n w : Nat} (hw : 1 ≤ w) (hn : w < n) (R : Queue)
    (hv : Valid n (unitPatternTarget n w R)) :
    complete (cycleAdjacent n) n (unitGainOccurrence n w R).source.2 0 ≠
      some ((unitPatternTarget n w R).2, 0, (unitGainOccurrence n w R).initiating) := by
  have hnd : (0 :: (unitInitialBlock n w ++ (R ++ unitTargetTail w))).Nodup := by
    simpa only [unitPatternTarget, List.singleton_append, List.append_assoc] using
      hv.nodup_iff.mpr List.nodup_range
  have htailnd : (0 :: (R ++ unitTargetTail w)).Nodup :=
    hnd.sublist ((List.sublist_append_right _ _).cons_cons 0)
  have hmem : 1 ∈ R ++ unitTargetTail w := by
    obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp (unit_pattern_last (w := w) (by omega) R)
    simp [hpre]
  have hcount := replacementCount_pos_of_neighbor hmem (cycle_consecutive (n := n) (i := 0) (by omega))
  have hlen : (reconstructedGain (cycleAdjacent n) (unitInitialBlock n w) 0 (R ++ unitTargetTail w)).length ≤ n := by
    have hh := hv.length_eq
    simp only [unitPatternTarget, List.length_append, List.length_singleton, List.length_range] at hh
    simp only [reconstructedGain, List.length_append, reverseInput_length]
    omega
  simpa only [unitGainOccurrence, unitPatternTarget, List.append_assoc] using
    reconstructedGain_changed (cycleAdjacent_symm n) (unitInitialBlock n w) (R ++ unitTargetTail w) 0 n htailnd hcount hlen

theorem unit_gained_predecessors {n w : Nat} {states : List State} (hw : 1 ≤ w) (hn : w < n)
    (hs : OrientationSupport n states) (R : Queue) (ht : unitPatternTarget n w R ∈ states)
    (hg : (unitGainOccurrence n w R).source ∈ states) :
    (gainedOccurrences (cycleAdjacent n) w n states (unitPatternTarget n w R)).Perm [unitGainOccurrence n w R] := by
  have hv := hs.valid _ ht
  let rest := (unitPatternTarget n w R).2
  have hnd : rest.Nodup := (List.nodup_cons.mp (hv.nodup_iff.mpr List.nodup_range)).2
  have hneigh : ∀ v ∈ rest, cycleAdjacent n v 0 = true → v = n - 1 ∨ v = 1 := by
    intro v hm he
    have hlabel := List.mem_range.mp (hv.second_subperm.subset hm)
    have hh := (cycleAdjacent_iff hlabel (show 0 < n by omega)).mp he
    omega
  have hidx : rest.idxOf (n - 1) + 1 = w := by
    simpa only [rest, unitPatternTarget, List.append_assoc] using
      unit_pattern_neighbor_index (by omega) hn (R ++ unitTargetTail w)
        (by simpa only [rest, unitPatternTarget, List.append_assoc] using hnd)
  have hlast : rest.getLast? = some 1 := unit_pattern_last (by omega) (unitInitialBlock n w ++ R)
  have htake : rest.take w = unitInitialBlock n w := by
    change (((unitInitialBlock n w ++ R) ++ unitTargetTail w).take w) = _
    rw [List.append_assoc]
    have hh : (unitInitialBlock n w ++ (R ++ unitTargetTail w)).take (unitInitialBlock n w).length =
        unitInitialBlock n w := by simp
    simpa only [unitInitialBlock_length] using hh
  have hdrop : rest.drop w = R ++ unitTargetTail w := by
    change (((unitInitialBlock n w ++ R) ++ unitTargetTail w).drop w) = _
    rw [List.append_assoc]
    have hh : (unitInitialBlock n w ++ (R ++ unitTargetTail w)).drop (unitInitialBlock n w).length =
        R ++ unitTargetTail w := by simp
    simpa only [unitInitialBlock_length] using hh
  have hc := unit_gain_complete hw hn R
  have hnc := unit_gain_changed hw hn R hv
  apply (List.perm_ext_iff_of_nodup (gainedOccurrences_nodup hs.nodup _) (by simp)).mpr
  intro o
  rw [List.mem_singleton, mem_gainedOccurrences]
  constructor
  · rintro ⟨ho, he, hnot⟩
    have hside : o.side = true := by
      cases hh : o.side with
      | true => rfl
      | false =>
        have hefalse := he
        rw [hh] at hefalse
        have hstable := first_singleton_budget_stable hw (by omega : 1 ≤ n) hefalse
        exact False.elim (hnot (by rw [hh]; exact hstable.symm.trans hefalse))
    rw [hside] at he hnot
    obtain ⟨hempty, hcomp⟩ := second_singleton_complete he
    have hcompnot : complete (cycleAdjacent n) n o.source.2 o.pos ≠ some (rest, 0, o.initiating) := by
      intro hc'
      apply hnot
      simp only [transition, if_true, hc', hempty, List.nil_append]
      rfl
    have hlen : o.source.2.length ≤ n := by
      have hh := (hs.valid _ ho).length_eq
      simpa only [hempty, List.nil_append, List.length_range] using hh.le
    obtain ⟨hp, hq⟩ := changed_predecessor_unique (cycleAdjacent_symm n) (by omega) hlen hnd hneigh hidx hlast hcomp hcompnot
    rw [htake, hdrop] at hq
    change o.source.2 = (unitGainOccurrence n w R).source.2 at hq
    have hsource : o.source = (unitGainOccurrence n w R).source := Prod.ext hempty hq
    have hinit : o.initiating = (unitGainOccurrence n w R).initiating := by
      rw [hp, hq, hc] at hcomp
      exact (congrArg (fun r : Queue × Nat × Nat => r.2.2) (Option.some.inj hcomp)).symm
    cases o
    simp_all only [unitGainOccurrence]
  · rintro rfl
    refine ⟨hg, ?_, ?_⟩
    · change transition (cycleAdjacent n) w (unitGainOccurrence n w R).source true 0 = _
      simp only [transition, if_true, hc]
      rfl
    · intro he
      exact hnc (second_singleton_complete he).2

end OddCycle
