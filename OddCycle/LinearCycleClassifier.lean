import OddCycle.ClassifierRuns
import OddCycle.CycleContinuousTime

/-! An executable linear-work recurrence classifier. The proof connects its
array implementation directly to the original queue's continuous-time return
event. The cost bound uses the word-RAM model stated in ClassifierRank. -/

namespace OddCycle.CycleClassifier

structure RunSummary where
  short : Bool
  full : Bool
  total : Nat
  count : Nat
  deriving Repr

def scanWork (w : Nat) : List Nat → Work RunSummary
  | [] => ⟨⟨true, true, 0, 0⟩, 1⟩
  | a :: q =>
    let r := scanWork w q
    ⟨⟨decide (a ≤ w) && r.value.short, decide (w ≤ a) && r.value.full,
      a + r.value.total, r.value.count + 1⟩, r.cost + 8⟩

theorem scanWork_spec (w : Nat) (q : List Nat) :
    ((scanWork w q).value.short = true ↔ ∀ a ∈ q, a ≤ w) ∧
    ((scanWork w q).value.full = true ↔ ∀ a ∈ q, w ≤ a) ∧
    (scanWork w q).value.total = q.sum ∧ (scanWork w q).value.count = q.length ∧
    (scanWork w q).cost = 8 * q.length + 1 := by
  induction q with
  | nil => simp [scanWork]
  | cons a q ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [scanWork, ih.1]
    · simp [scanWork, ih.2.1]
    · simp [scanWork, ih.2.2.1]
    · simp [scanWork, ih.2.2.2.1]
    · simp [scanWork, ih.2.2.2.2]; omega

def testWork (w : Nat) (q : List Nat) : Work Bool :=
  let r := scanWork w q
  ⟨r.value.short || (r.value.full && decide (r.value.total = w * r.value.count + 1)), r.cost + 5⟩

theorem testWork_spec (w : Nat) (q : List Nat) :
    ((testWork w q).value = true ↔ CircularRun.Short w q ∨ CircularRun.Exceptional w q) ∧
    (testWork w q).cost = 8 * q.length + 6 := by
  have hh := scanWork_spec w q
  constructor
  · simp only [testWork, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, CircularRun.Short, CircularRun.Exceptional]
  · simp only [testWork, hh.2.2.2.2]

def classify (n w : Nat) (s : State) : Work Bool :=
  let p := placementWork s
  let a := ranks n p.value
  let b := bitsLoop n a.value n 0
  let r := runsWork b.value
  let t := testWork w r.value
  ⟨t.value, p.cost + a.cost + b.cost + r.cost + t.cost⟩

theorem classify_correct {n w : Nat} {s : State} (hn : 0 < n) (hs : Valid n s) :
    (classify n w s).value = true ↔ ShortRuns n w s ∨ ExceptionalRuns n w s := by
  simp only [classify, (testWork_spec _ _).1, (runsWork_spec _).1, (placementWork_spec s).1,
    ranked_orientation hn hs, ShortRuns, ExceptionalRuns, cycleRuns]

theorem classify_cost {n w : Nat} {s : State} (hn : 0 < n) (hs : Valid n s) :
    (classify n w s).cost ≤ 33 * n + 18 := by
  have hp := placementWork_spec s
  have hlen : s.1.length + s.2.length = n := by
    simpa only [List.length_append, List.length_range] using hs.length_eq
  have hplen : (placementWork s).value.length = n := by
    rw [hp.1]
    simpa using hs.placement_perm.length_eq
  have ha := ranks_cost n (placementWork s).value
  have hb := bitsLoop_cost n (ranks n (placementWork s).value).value n 0
  have hr := runsWork_spec (bitsLoop n (ranks n (placementWork s).value).value n 0).value
  have ht := (testWork_spec w (runsWork (bitsLoop n (ranks n (placementWork s).value).value n 0).value).value).2
  have hbits : (bitsLoop n (ranks n (placementWork s).value).value n 0).value = orientation n s := by
    rw [hp.1]
    exact ranked_orientation hn hs
  have hrunlen : (runsWork (bitsLoop n (ranks n (placementWork s).value).value n 0).value).value.length ≤ n := by
    rw [hr.1, hbits]
    have hh := List.length_le_sum_of_one_le (cycleRuns n s) (fun a ha => cycleRuns_positive n s a ha)
    rw [cycleRuns_sum] at hh
    exact hh
  have hblen : (bitsLoop n (ranks n (placementWork s).value).value n 0).value.length = n := by
    rw [hbits, orientation_length]
  simp only [hplen] at ha
  simp only [hblen] at hr
  simp only [classify]
  omega

theorem classify_terminal {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w) (s : CycleState n) :
    (classify n w s.val).value = true ↔ ReachabilityQuotient.Terminal (CycleState.Step n w) s :=
  (classify_correct (by omega) s.property).trans (CycleState.terminal_iff_runs hn hw s).symm

theorem classify_continuous_recurrence {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w)
    (a : PositivePositionAllocation n) (s : CycleState n) :
    ((classify n w s.val).value = true ↔
      a.pathLaw (by omega) w s (FiniteMarkov.continuousReturn a.total (a.total_pos (by omega)) s) = 1) ∧
    (classify n w s.val).cost ≤ 33 * n + 18 :=
  ⟨(classify_correct (by omega) s.property).trans (a.continuous_recurrent_iff_runs hn hw s).symm,
    classify_cost (by omega) s.property⟩

end OddCycle.CycleClassifier
