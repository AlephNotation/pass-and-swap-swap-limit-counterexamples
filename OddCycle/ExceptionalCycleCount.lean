import OddCycle.BinaryMoment

/-! Exactly `2*n` exceptional orientations: every parameter is represented,
and its rotation and bit are determined uniquely by the orientation. -/

namespace OddCycle

theorem full_encoding_count (w k : Nat) (b : Bool) :
    (CircularWord.encode b (List.replicate (2 * k) w)).count true = k * w := by
  induction k generalizing b with
  | zero => simp [CircularWord.encode]
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, List.replicate_succ, List.replicate_succ]
    simp only [CircularWord.encode, Bool.not_not, List.count_append, ih]
    cases b <;> simp [Nat.add_mul, List.count_replicate] <;> omega

theorem exceptional_encoding_eq_cons {w k : Nat} (hk : 1 ≤ k) (b : Bool) :
    CircularWord.encode b (exceptionalRunList w k) =
      b :: CircularWord.encode b (List.replicate (2 * k) w) := by
  have he : 2 * k = (2 * k - 1) + 1 := by omega
  conv_rhs => rw [he, List.replicate_succ, CircularWord.encode]
  simp only [exceptionalRunList, CircularWord.encode, List.replicate_succ, List.cons_append]

theorem exceptional_encoding_count {w k : Nat} (hk : 1 ≤ k) (b : Bool) :
    (CircularWord.encode b (exceptionalRunList w k)).count true = if b then k * w + 1 else k * w := by
  rw [exceptional_encoding_eq_cons hk b]
  cases b <;> simp [full_encoding_count]

theorem exceptionalParameterWord_count {n w k : Nat} (hk : 1 ≤ k) (p : ExceptionalCycle.Parameter n) :
    (exceptionalParameterWord n w k p).count true = if p.2 then k * w + 1 else k * w := by
  have hh := (List.rotate_perm (CircularWord.encode p.2 (exceptionalRunList w k)) p.1.val).count_eq true
  simpa only [exceptional_encoding_count hk] using hh

theorem exceptionalParameter_injective {n w k : Nat} (hn : n = 2 * k * w + 1)
    (hw : 1 ≤ w) (hk : 1 ≤ k) : Function.Injective (exceptionalParameterState hn hw hk) := by
  letI : NeZero n := ⟨by omega⟩
  rintro ⟨a, b⟩ ⟨c, d⟩ he
  have hword := congrArg Subtype.val he
  have hcount := congrArg (List.count true) hword
  change (exceptionalParameterWord n w k (a, b)).count true =
    (exceptionalParameterWord n w k (c, d)).count true at hcount
  rw [exceptionalParameterWord_count hk, exceptionalParameterWord_count hk] at hcount
  have hbd : b = d := by cases b <;> cases d <;> simp_all
  subst d
  let q := CircularWord.encode b (exceptionalRunList w k)
  have hlen : q.length = n := by simp only [q, CircularWord.encode_length, exceptionalRunList_sum hk, hn]
  let f := CircularWord.cyclicBit q hlen
  have hmass := CircularWord.cyclicBit_mass q hlen
  have hnz : (2 : ZMod n) * k * w + 1 = 0 := by
    have hh : ((2 * k * w + 1 : Nat) : ZMod n) = 0 := by rw [← hn, ZMod.natCast_self]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hh
  have hm : 2 * CircularWord.bitMass f = 1 ∨ 2 * CircularWord.bitMass f = -1 := by
    change 2 * CircularWord.bitMass (CircularWord.cyclicBit q hlen) = 1 ∨
      2 * CircularWord.bitMass (CircularWord.cyclicBit q hlen) = -1
    rw [hmass]
    change 2 * ((CircularWord.encode b (exceptionalRunList w k)).count true : ZMod n) = 1 ∨
      2 * ((CircularWord.encode b (exceptionalRunList w k)).count true : ZMod n) = -1
    rw [exceptional_encoding_count hk]
    cases b with
    | false =>
      right
      simp only [Bool.false_eq_true, if_false, Nat.cast_mul]
      calc
        _ = ((2 : ZMod n) * k * w + 1) - 1 := by ring
        _ = -1 := by rw [hnz, zero_sub]
    | true =>
      left
      simp only [if_true, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      calc
        _ = ((2 : ZMod n) * k * w + 1) + 1 := by ring
        _ = 1 := by rw [hnz, zero_add]
  have hac : a = c := by
    apply CircularWord.shift_injective_of_half_mass hm
    intro i
    change q.rotate a.val = q.rotate c.val at hword
    have hh : CircularWord.cyclicBit (q.rotate a.val) (by simpa using hlen) i =
        CircularWord.cyclicBit (q.rotate c.val) (by simpa using hlen) i := by
      unfold CircularWord.cyclicBit
      simp only [hword]
    exact (CircularWord.cyclicBit_rotate q hlen a i).symm.trans
      (hh.trans (CircularWord.cyclicBit_rotate q hlen c i))
  simp only [hac]

abbrev ExceptionalOrientation (n w : Nat) :=
  {q : BinaryCycle n // CircularRun.Exceptional w (CircularWord.circularRuns q.val)}

noncomputable def exceptionalOrientationEquiv {n w k : Nat} (hn : n = 2 * k * w + 1)
    (hw : 1 ≤ w) (hk : 1 ≤ k) : ExceptionalCycle.Parameter n ≃ ExceptionalOrientation n w :=
  Equiv.ofBijective
    (fun p => ⟨exceptionalParameterState hn hw hk p, by
      have hr := CircularWord.circularRuns_isRotated (exceptional_encoding_nonconstant hw hk p.2)
        (show List.IsRotated (CircularWord.encode p.2 (exceptionalRunList w k))
          (exceptionalParameterWord n w k p) from ⟨p.1.val, rfl⟩)
      exact CircularRun.exceptional_reachable (exceptional_encoding_runs hw hk p.2)
        (CircularRun.Reach.of_isRotated hr.symm)⟩)
    ⟨fun _ _ he => exceptionalParameter_injective hn hw hk (congrArg Subtype.val he),
      fun q => by
        obtain ⟨p, hp⟩ := exceptionalParameter_covers hn hw hk q.val q.property
        exact ⟨p, Subtype.ext hp⟩⟩

theorem exceptional_orientation_count {n w k : Nat} (hn : n = 2 * k * w + 1)
    (hw : 1 ≤ w) (hk : 1 ≤ k) : Nat.card (ExceptionalOrientation n w) = 2 * n := by
  letI : NeZero n := ⟨by omega⟩
  rw [Nat.card_congr (exceptionalOrientationEquiv hn hw hk).symm, Nat.card_eq_fintype_card,
    ExceptionalCycle.parameter_count]

end OddCycle
