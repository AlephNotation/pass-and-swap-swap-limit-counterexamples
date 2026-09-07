import OddCycle.ExceptionalCycleClass

/-! The exceptional orientations form one communicating component. The
parameter is a left-rotation offset and a bit, so its negative is the edge
at which the long run begins. -/

namespace OddCycle.CircularWord

theorem encode_rotate_runs (b : Bool) (p q : List Nat) (heven : Even (p ++ q).length) :
    (encode b (p ++ q)).rotate (encode b p).length = encode (phase b p.length) (q ++ p) := by
  have hp : phase (phase b p.length) q.length = b := by
    rw [Nat.even_iff, List.length_append] at heven
    rw [← phase_add]
    simp only [phase, heven, if_true]
  rw [encode_append, encode_append, hp]
  exact List.rotate_append_length_eq _ _

theorem full_cycle_slide (w m : Nat) (b : Bool) (hm : m % 2 = 1) :
    encode b (List.replicate m w) ++ List.replicate w (!b) =
      List.replicate w b ++ encode (!b) (List.replicate m w) := by
  calc
    _ = encode b (List.replicate m w ++ [w]) := by
      rw [encode_append]
      simp only [List.length_replicate, phase_odd b hm, encode, List.append_nil]
    _ = encode b (w :: List.replicate m w) := by rw [← List.replicate_succ', List.replicate_succ]
    _ = _ := rfl

end OddCycle.CircularWord

namespace OddCycle

theorem exceptional_canonical_step {w k : Nat} (hk : 1 ≤ k) (b : Bool) :
    CircularWord.CircularFlip w (CircularWord.encode b (exceptionalRunList w k))
      ((CircularWord.encode (!b) (exceptionalRunList w k)).rotate w) := by
  let tail := CircularWord.encode (!b) (List.replicate (2 * k - 1) w)
  have hm : (2 * k - 1) % 2 = 1 := by omega
  have htarget : (CircularWord.encode (!b) (exceptionalRunList w k)).rotate w =
      (!b) :: (List.replicate w b ++ tail) := by
    change (List.replicate (w + 1) (!b) ++
      CircularWord.encode (!!b) (List.replicate (2 * k - 1) w)).rotate w = _
    rw [Bool.not_not, List.replicate_succ', List.append_assoc]
    have hh := List.rotate_append_length_eq (List.replicate w (!b))
      ([!b] ++ CircularWord.encode b (List.replicate (2 * k - 1) w))
    simp only [List.length_replicate] at hh
    rw [hh]
    simpa only [List.singleton_append, List.cons_append] using
      congrArg (Bool.not b :: ·) (CircularWord.full_cycle_slide w (2 * k - 1) b hm)
  refine ⟨0, ?_⟩
  simp only [List.rotate_zero, htarget]
  exact CircularWord.LinearFlip.first [] tail b

def exceptionalParameterWord (n w k : Nat) (p : ExceptionalCycle.Parameter n) : List Bool :=
  (CircularWord.encode p.2 (exceptionalRunList w k)).rotate p.1.val

def exceptionalParameterState {n w k : Nat} (hn : n = 2 * k * w + 1) (hw : 1 ≤ w) (hk : 1 ≤ k)
    (p : ExceptionalCycle.Parameter n) : BinaryCycle n :=
  ⟨exceptionalParameterWord n w k p, by
    simp only [exceptionalParameterWord, List.length_rotate, CircularWord.encode_length,
      exceptionalRunList_sum hk, hn],
    (exceptional_encoding_nonconstant hw hk p.2).perm (List.rotate_perm _ _).symm⟩

theorem exceptionalParameter_step {n w k : Nat} (hn : n = 2 * k * w + 1) (hw : 1 ≤ w) (hk : 1 ≤ k)
    {p q : ExceptionalCycle.Parameter n} (h : ExceptionalCycle.Step n w p q) :
    BinaryCycle.Step n w (exceptionalParameterState hn hw hk p) (exceptionalParameterState hn hw hk q) := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨a, b⟩ := p
  change q = (a + w, !b) at h
  subst q
  have hc := exceptional_canonical_step (w := w) hk b
  have hl : (CircularWord.encode b (exceptionalRunList w k)).length =
      ((CircularWord.encode (!b) (exceptionalRunList w k)).rotate w).length := by
    simp only [List.length_rotate, CircularWord.encode_length]
  have hh := (CircularWord.CircularFlip.rotate_iff (k := a.val) hl).mpr hc
  have hlen : (CircularWord.encode (!b) (exceptionalRunList w k)).length = n := by
    simp only [CircularWord.encode_length, exceptionalRunList_sum hk, hn]
  have hval : (a + (w : ZMod n)).val = (a.val + w) % n := by
    simp [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
  change CircularWord.CircularFlip w
    ((CircularWord.encode b (exceptionalRunList w k)).rotate a.val)
    ((CircularWord.encode (!b) (exceptionalRunList w k)).rotate (a + (w : ZMod n)).val)
  rw [hval]
  have hr := List.rotate_mod (CircularWord.encode (!b) (exceptionalRunList w k)) (a.val + w)
  rw [hlen] at hr
  rw [hr]
  simpa only [List.rotate_rotate, Nat.add_comm] using hh

theorem exceptionalParameter_communication {n w k : Nat} (hn : n = 2 * k * w + 1)
    (hw : 1 ≤ w) (hk : 1 ≤ k) (p q : ExceptionalCycle.Parameter n) :
    Relation.ReflTransGen (BinaryCycle.Step n w)
      (exceptionalParameterState hn hw hk p) (exceptionalParameterState hn hw hk q) :=
  Relation.ReflTransGen.lift (exceptionalParameterState hn hw hk)
    (fun _ _ hs => exceptionalParameter_step hn hw hk hs) (ExceptionalCycle.communication hn p q)

theorem exceptionalParameter_covers {n w k : Nat} (hn : n = 2 * k * w + 1)
    (hw : 1 ≤ w) (hk : 1 ≤ k) (q : BinaryCycle n)
    (hq : CircularRun.Exceptional w (CircularWord.circularRuns q.val)) :
    ∃ p : ExceptionalCycle.Parameter n, exceptionalParameterState hn hw hk p = q := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨pre, post, hr, hfull⟩ := CircularRun.exceptional_iff_one_long.mp hq
  have hsum := CircularWord.circularRuns_sum q.val
  rw [q.property.1] at hsum
  have hlen : (CircularWord.circularRuns q.val).length = 2 * k := by
    have htotal := hq.2
    rw [hsum] at htotal
    nlinarith [hn]
  have hp : ∀ a ∈ post ++ pre, a = w := by simpa only [List.mem_append, or_comm] using hfull
  have htail : post ++ pre = List.replicate (2 * k - 1) w := by
    apply List.eq_replicate_iff.mpr
    refine ⟨?_, hp⟩
    rw [hr] at hlen
    simp only [List.length_append, List.length_cons] at hlen ⊢
    omega
  obtain ⟨b, hb⟩ := CircularWord.circular_encoding_rotated q.val
  let c := CircularWord.phase b pre.length
  have hrot : List.IsRotated (CircularWord.encode b (CircularWord.circularRuns q.val))
      (CircularWord.encode c (exceptionalRunList w k)) := by
    refine ⟨(CircularWord.encode b pre).length, ?_⟩
    rw [hr, CircularWord.encode_rotate_runs b pre ((w + 1) :: post)]
    · simp only [List.cons_append, htail, exceptionalRunList, c]
    · simpa only [hr] using CircularWord.circularRuns_even q.property.2
  obtain ⟨i, hi⟩ := hrot.symm.trans hb
  refine ⟨((i : ZMod n), c), ?_⟩
  apply Subtype.ext
  change (CircularWord.encode c (exceptionalRunList w k)).rotate (i : ZMod n).val = q.val
  rw [ZMod.val_natCast]
  have hcanlen : (CircularWord.encode c (exceptionalRunList w k)).length = n := by
    simp only [CircularWord.encode_length, exceptionalRunList_sum hk, hn]
  have hh := List.rotate_mod (CircularWord.encode c (exceptionalRunList w k)) i
  rw [hcanlen] at hh
  exact hh.trans hi

/-- All actual exceptional queue states communicate, including different
orientations, linear extensions, and queue cuts. -/
theorem exceptionalRuns_communicate {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w)
    {s t : State} (hs : Valid n s) (ht : Valid n t)
    (hsex : ExceptionalRuns n w s) (htex : ExceptionalRuns n w t) :
    EventReachable (cycleAdjacent n) w s t := by
  obtain ⟨k, hk, hnk⟩ := exceptionalRuns_cycle_length (by omega) hs hsex
  let a := CycleState.binaryProject hn ⟨s, hs⟩
  let b := CycleState.binaryProject hn ⟨t, ht⟩
  obtain ⟨p, hp⟩ := exceptionalParameter_covers hnk hw hk a hsex
  obtain ⟨q, hq⟩ := exceptionalParameter_covers hnk hw hk b htex
  apply (CycleState.reachable_iff_binary hn hw ⟨s, hs⟩ ⟨t, ht⟩).mpr
  have hh := exceptionalParameter_communication hnk hw hk p q
  simpa only [hp, hq] using hh

end OddCycle
