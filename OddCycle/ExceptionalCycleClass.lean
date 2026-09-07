import OddCycle.OperationalCycleClassification

/-! Existence and eventwise closure of the exceptional cycle states. These
closure claims quantify over every legal completion, independently of rates. -/

namespace OddCycle

theorem CircularRun.exceptional_reachable {w : Nat} {r s : List Nat}
    (hr : CircularRun.Exceptional w r) (h : CircularRun.Reach w r s) : CircularRun.Exceptional w s := by
  induction h with
  | refl => exact hr
  | tail _ hs ih => exact (CircularRun.exceptional_step ih hs).1

theorem CircularRun.Exceptional.not_short {w : Nat} {r : List Nat}
    (h : CircularRun.Exceptional w r) : ¬ CircularRun.Short w r := by
  obtain ⟨pre, post, rfl, _⟩ := CircularRun.exceptional_iff_one_long.mp h
  intro hs
  have hh := hs (w + 1) (by simp)
  omega

theorem CycleState.reachable_runs {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w) {s t : CycleState n}
    (h : EventReachable (cycleAdjacent n) w s.val t.val) :
    CircularRun.Reach w (cycleRuns n s.val) (cycleRuns n t.val) := by
  have hb := (CycleState.reachable_iff_binary hn hw s t).mp h
  have ha : CircularWord.AugmentedReach w (orientation n s.val) (orientation n t.val) :=
    Relation.ReflTransGen.lift' Subtype.val (fun _ _ hs => hs.augmentedReach) hb
  exact (ha.project hw (orientation_nonconstant (by omega) s.property)).2

theorem exceptionalRuns_reachable {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w)
    {s t : State} (hs : Valid n s) (ht : Valid n t) (hex : ExceptionalRuns n w s)
    (h : EventReachable (cycleAdjacent n) w s t) : ExceptionalRuns n w t :=
  CircularRun.exceptional_reachable hex
    (CycleState.reachable_runs hn hw (s := ⟨s, hs⟩) (t := ⟨t, ht⟩) h)

/-- Every position completion preserves the exceptional family. Zero-rate
events can therefore be removed without destroying closure. -/
theorem exceptionalRuns_transition {n w pos initiating : Nat} {s t : State} {side : Bool}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hs : Valid n s) (hex : ExceptionalRuns n w s)
    (he : transition (cycleAdjacent n) w s side pos = some (t, initiating)) : ExceptionalRuns n w t :=
  exceptionalRuns_reachable hn hw hs (transition_valid hs he) hex (.single ⟨side, pos, initiating, he⟩)

def exceptionalRunList (w k : Nat) : List Nat := (w + 1) :: List.replicate (2 * k - 1) w

theorem exceptionalRunList_length {w k : Nat} (hk : 1 ≤ k) : (exceptionalRunList w k).length = 2 * k := by
  simp only [exceptionalRunList, List.length_cons, List.length_replicate]
  omega

theorem exceptionalRunList_sum {w k : Nat} (hk : 1 ≤ k) :
    (exceptionalRunList w k).sum = 2 * k * w + 1 := by
  have he : 2 * k = (2 * k - 1) + 1 := by omega
  simp only [exceptionalRunList, List.sum_cons, List.sum_replicate, smul_eq_mul]
  conv_rhs => rw [he]
  ring

theorem exceptionalRunList_positive {w k : Nat} (hw : 1 ≤ w) :
    ∀ a ∈ exceptionalRunList w k, 0 < a := by
  intro a ha
  simp only [exceptionalRunList, List.mem_cons, List.mem_replicate] at ha
  rcases ha with rfl | ⟨_, rfl⟩ <;> omega

theorem exceptionalRunList_exceptional (w k : Nat) : CircularRun.Exceptional w (exceptionalRunList w k) := by
  apply CircularRun.exceptional_iff_one_long.mpr
  exact ⟨[], List.replicate (2 * k - 1) w, rfl, by simp⟩

theorem exceptionalRunList_even {w k : Nat} (hk : 1 ≤ k) : Even (exceptionalRunList w k).length := by
  rw [exceptionalRunList_length hk]
  exact even_two_mul k

theorem exceptional_encoding_nonconstant {w k : Nat} (hw : 1 ≤ w) (hk : 1 ≤ k) (b : Bool) :
    CircularWord.Nonconstant (CircularWord.encode b (exceptionalRunList w k)) := by
  have he : 2 * k - 1 = (2 * k - 2) + 1 := by omega
  rw [exceptionalRunList, he, List.replicate_succ]
  exact CircularWord.encode_nonconstant (by omega) (by omega)

theorem exceptional_encoding_runs {w k : Nat} (hw : 1 ≤ w) (hk : 1 ≤ k) (b : Bool) :
    CircularRun.Exceptional w (CircularWord.circularRuns (CircularWord.encode b (exceptionalRunList w k))) := by
  have hrot := CircularWord.circularRuns_rotate_encode 0 b (exceptionalRunList w k)
    (by simp [exceptionalRunList]) (exceptionalRunList_positive hw) (exceptionalRunList_even hk)
  simp only [List.rotate_zero] at hrot
  exact CircularRun.exceptional_reachable (exceptionalRunList_exceptional w k)
    (CircularRun.Reach.of_isRotated hrot.symm)

theorem exceptionalRuns_exists {n w k : Nat} (hw : 1 ≤ w) (hk : 1 ≤ k) (hn : n = 2 * k * w + 1) :
    ∃ s, Valid n s ∧ ExceptionalRuns n w s := by
  let q := CircularWord.encode false (exceptionalRunList w k)
  have hlen : q.length = n := by simp only [q, CircularWord.encode_length, exceptionalRunList_sum hk, hn]
  obtain ⟨s, hs, ho⟩ := orientation_surjective hlen (exceptional_encoding_nonconstant hw hk false)
  refine ⟨s, hs, ?_⟩
  change CircularRun.Exceptional w (CircularWord.circularRuns (orientation n s))
  rw [ho]
  exact exceptional_encoding_runs hw hk false

theorem exceptionalRuns_tall {n w : Nat} (hn : 3 ≤ n) {s : State} (hs : Valid n s)
    (hex : ExceptionalRuns n w s) : w < height n s := by
  have hnot := CircularRun.Exceptional.not_short hex
  have hh := shortRuns_iff_height (w := w) (by omega) hs
  change ¬ ShortRuns n w s at hnot
  exact Nat.lt_of_not_ge (fun hle => hnot (hh.mpr hle))

/-- Exact arithmetic criterion for the existence of a tall terminal event
component, now proved for the original queue configurations. -/
theorem exists_tall_terminal_iff {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w) :
    (∃ s : CycleState n, ReachabilityQuotient.Terminal (CycleState.Step n w) s ∧ w < height n s.val) ↔
      ∃ k, 1 ≤ k ∧ n = 2 * k * w + 1 := by
  constructor
  · rintro ⟨s, hs, htall⟩
    rcases (CycleState.terminal_iff_runs hn hw s).mp hs with hshort | hex
    · have hh := (shortRuns_iff_height (by omega) s.property).mp hshort
      omega
    · exact exceptionalRuns_cycle_length (by omega) s.property hex
  · rintro ⟨k, hk, hn'⟩
    obtain ⟨s, hs, hex⟩ := exceptionalRuns_exists hw hk hn'
    exact ⟨⟨s, hs⟩, CycleState.exceptional_terminal hn hw ⟨s, hs⟩ hex, exceptionalRuns_tall hn hs hex⟩

end OddCycle
