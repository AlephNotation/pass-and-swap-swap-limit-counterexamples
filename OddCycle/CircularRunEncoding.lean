import OddCycle.CircularWords

/-! Uniqueness and maximality of positive alternating-block encodings. -/

namespace OddCycle.CircularWord

theorem lengthsFrom_boundary (b : Bool) (q : List Bool) (h : q.head? ≠ some b) :
    lengthsFrom b q = 1 :: linearRuns q := by
  cases q with
  | nil => rfl
  | cons c q =>
    have hb : b ≠ c := by simpa [eq_comm] using h
    simp [lengthsFrom, linearRuns, hb]

theorem lengthsFrom_replicate_append (b : Bool) (m : Nat) (q : List Bool)
    (h : q.head? ≠ some b) :
    lengthsFrom b (List.replicate m b ++ q) = (m + 1) :: linearRuns q := by
  induction m with
  | zero => simpa using lengthsFrom_boundary b q h
  | succ m ih => simp [List.replicate_succ, lengthsFrom, ih, bump]

/-- Positive alternating blocks are precisely the maximal linear runs. -/
theorem linearRuns_encode (b : Bool) (r : List Nat) (hpos : ∀ a ∈ r, 0 < a) :
    linearRuns (encode b r) = r := by
  induction r generalizing b with
  | nil => rfl
  | cons a r ih =>
    have ha := hpos a (by simp)
    have ht : ∀ x ∈ r, 0 < x := fun x hx => hpos x (by simp [hx])
    have hb : (encode (!b) r).head? ≠ some b := by
      cases r with
      | nil => simp [encode]
      | cons c r => rw [encode_head (ht c (by simp))]; simp
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    change lengthsFrom b (List.replicate m b ++ encode (!b) r) = (m + 1) :: r
    rw [lengthsFrom_replicate_append b m _ hb, ih (!b) ht]

theorem encode_injective_lengths {b c : Bool} {r s : List Nat}
    (hr : ∀ a ∈ r, 0 < a) (hs : ∀ a ∈ s, 0 < a)
    (h : encode b r = encode c s) : r = s := by
  simpa only [linearRuns_encode b r hr, linearRuns_encode c s hs] using congrArg linearRuns h

theorem phase_odd (b : Bool) {m : Nat} (hm : m % 2 = 1) : phase b m = !b := by
  simp [phase, hm]

theorem encode_rotate_first {b : Bool} {a : Nat} {r : List Nat}
    (heven : Even (a :: r).length) :
    (encode b (a :: r)).rotate a = encode (!b) (r ++ [a]) := by
  have hp : r.length % 2 = 1 := by rw [Nat.even_iff] at heven; simp only [List.length_cons] at heven; omega
  rw [encode_append, phase_odd (!b) hp, Bool.not_not]
  change (List.replicate a b ++ encode (!b) r).rotate a = encode (!b) r ++ (List.replicate a b ++ [])
  simpa using List.rotate_append_length_eq (List.replicate a b) (encode (!b) r)

theorem circularRuns_encode {b : Bool} {a : Nat} {r : List Nat}
    (hpos : ∀ x ∈ a :: r, 0 < x) (heven : Even (a :: r).length) :
    circularRuns (encode b (a :: r)) = r ++ [a] := by
  rw [circularRuns, linearRuns_encode b _ hpos, List.headD_cons, encode_rotate_first heven]
  apply linearRuns_encode
  intro x hx
  apply hpos x
  simpa [or_comm] using hx

theorem linearRuns_replicate_append (b : Bool) {m : Nat} (q : List Bool)
    (hm : 0 < m) (hq : q.head? ≠ some b) :
    linearRuns (List.replicate m b ++ q) = m :: linearRuns q := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  exact lengthsFrom_replicate_append b m q hq

/-- Changing the cut within a run does not split that circular run. -/
theorem circularRuns_rotate_inside {b : Bool} {a k : Nat} {r : List Nat}
    (hpos : ∀ x ∈ a :: r, 0 < x) (heven : Even (a :: r).length) (hk : k < a) :
    circularRuns ((encode b (a :: r)).rotate k) = r ++ [a] := by
  have hr : r ≠ [] := by
    intro hr
    rw [hr, Nat.even_iff] at heven
    simp at heven
  have hhead : (encode (!b) r).head? = some (!b) := by
    cases r with
    | nil => exact False.elim (hr rfl)
    | cons c r => exact encode_head (hpos c (by simp))
  have hne : encode (!b) r ≠ [] := by intro h; simp [h] at hhead
  have hrpar : r.length % 2 = 1 := by
    rw [Nat.even_iff] at heven
    simp only [List.length_cons] at heven
    omega
  have hrep : List.replicate a b = List.replicate k b ++ List.replicate (a - k) b := by
    rw [← List.replicate_add]
    congr 1
    omega
  have hrot : (encode b (a :: r)).rotate k =
      List.replicate (a - k) b ++ (encode (!b) r ++ List.replicate k b) := by
    change (List.replicate a b ++ encode (!b) r).rotate k = _
    rw [hrep, List.append_assoc]
    simpa only [List.length_replicate, List.append_assoc] using
      List.rotate_append_length_eq (List.replicate k b)
        (List.replicate (a - k) b ++ encode (!b) r)
  have htail : (encode (!b) r ++ List.replicate k b).head? ≠ some b := by
    rw [List.head?_append_of_ne_nil _ hne, hhead]
    simp
  rw [hrot, circularRuns, linearRuns_replicate_append b _ (by omega) htail, List.headD_cons]
  have hh := List.rotate_append_length_eq (List.replicate (a - k) b)
    (encode (!b) r ++ List.replicate k b)
  simp only [List.length_replicate] at hh
  rw [hh]
  have hword : (encode (!b) r ++ List.replicate k b) ++ List.replicate (a - k) b =
      encode (!b) (r ++ [a]) := by
    rw [encode_append, phase_odd (!b) hrpar, Bool.not_not]
    simp only [encode, List.append_nil, List.append_assoc, ← List.replicate_add]
    congr 2
    omega
  rw [hword]
  apply linearRuns_encode
  intro x hx
  apply hpos x
  simpa [or_comm] using hx

/-- The extracted circular run list is independent of the edge chosen as
index zero, up to reselecting the first run. -/
theorem circularRuns_rotate_encode (k : Nat) (b : Bool) (r : List Nat)
    (hr : r ≠ []) (hpos : ∀ a ∈ r, 0 < a) (heven : Even r.length) :
    List.IsRotated (circularRuns ((encode b r).rotate k)) r := by
  induction k using Nat.strong_induction_on generalizing b r with
  | h k ih =>
    cases r with
    | nil => exact False.elim (hr rfl)
    | cons a r =>
      by_cases hk : k < a
      · rw [circularRuns_rotate_inside hpos heven hk]
        exact List.isRotated_concat a r
      · have ha := hpos a (by simp)
        have hp : ∀ x ∈ r ++ [a], 0 < x := by
          intro x hx
          apply hpos x
          simpa [or_comm] using hx
        have hev : Even (r ++ [a]).length := by simpa using heven
        have hh := ih (k - a) (by omega) (!b) (r ++ [a]) (by simp) hp hev
        have hrot : (encode b (a :: r)).rotate k =
            (encode (!b) (r ++ [a])).rotate (k - a) := by
          rw [← encode_rotate_first heven, List.rotate_rotate]
          congr 1
          omega
        rw [hrot]
        exact hh.trans (List.isRotated_concat a r)

theorem circular_encoding_rotated (q : List Bool) :
    ∃ b, List.IsRotated (encode b (circularRuns q)) q := by
  let z := q.rotate ((linearRuns q).headD 0)
  refine ⟨z.headD false, ?_⟩
  have he : encode (z.headD false) (circularRuns q) = z := encode_linearRuns z
  rw [he]
  exact List.IsRotated.forall q _

theorem circularRuns_nonempty {q : List Bool} (hq : Nonconstant q) : circularRuns q ≠ [] := by
  intro hr
  have hh := circularRuns_sum q
  rw [hr] at hh
  have hnil : q = [] := List.length_eq_zero_iff.mp hh.symm
  simp [hnil, Nonconstant] at hq

theorem circularRuns_isRotated {q z : List Bool} (hq : Nonconstant q)
    (hrot : List.IsRotated q z) : List.IsRotated (circularRuns z) (circularRuns q) := by
  obtain ⟨b, hb⟩ := circular_encoding_rotated q
  obtain ⟨k, hk⟩ := hb.trans hrot
  rw [← hk]
  exact circularRuns_rotate_encode k b (circularRuns q) (circularRuns_nonempty hq)
    (circularRuns_positive q) (circularRuns_even hq)

theorem lengthsFrom_not (b : Bool) (q : List Bool) :
    lengthsFrom (!b) (q.map Bool.not) = lengthsFrom b q := by
  induction q generalizing b with
  | nil => rfl
  | cons c q ih => simp [lengthsFrom, ih]

theorem linearRuns_not (q : List Bool) : linearRuns (q.map Bool.not) = linearRuns q := by
  cases q with
  | nil => rfl
  | cons b q => exact lengthsFrom_not b q

theorem circularRuns_not (q : List Bool) : circularRuns (q.map Bool.not) = circularRuns q := by
  simp only [circularRuns, linearRuns_not, ← List.map_rotate, linearRuns_not]

theorem phase_not (b : Bool) (m : Nat) : phase (!b) m = !(phase b m) := by
  simp only [phase]
  split_ifs <;> simp

theorem phase_add (b : Bool) (m k : Nat) : phase b (m + k) = phase (phase b m) k := by
  induction m generalizing b with
  | zero => simp
  | succ m ih => simpa only [Nat.succ_add, phase_succ] using ih (!b)

theorem phase_twice (b : Bool) (m : Nat) : phase (phase b m) m = b := by
  rw [← phase_add]
  simp [phase, Nat.add_mod]
  have hm := Nat.mod_lt m (by omega : 0 < 2)
  omega

theorem encode_reverse (b : Bool) (r : List Nat) :
    (encode b r).reverse = encode (phase b (r.length - 1)) r.reverse := by
  induction r generalizing b with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => simp [encode]
    | cons c r =>
      change (List.replicate a b ++ encode (!b) (c :: r)).reverse = _
      rw [List.reverse_append, ih, List.reverse_replicate]
      conv_rhs => rw [List.reverse_cons]
      rw [encode_append]
      have hphase : phase b ((a :: c :: r).length - 1) = phase (!b) ((c :: r).length - 1) := by
        simp [phase_succ]
      rw [hphase]
      have hlast : phase (phase (!b) ((c :: r).length - 1)) (c :: r).reverse.length = b := by
        simp only [List.length_reverse, List.length_cons, Nat.add_sub_cancel, phase_succ,
          ← phase_not, Bool.not_not, phase_twice]
      rw [hlast]
      simp [encode]

theorem linearRuns_reverse (q : List Bool) : linearRuns q.reverse = (linearRuns q).reverse := by
  have he := encode_linearRuns q
  have hr := encode_reverse (q.headD false) (linearRuns q)
  rw [he] at hr
  rw [hr, linearRuns_encode]
  intro a ha
  exact linearRuns_positive q a (by simpa using ha)

theorem lengthsFrom_head_positive (b : Bool) (q : List Bool) :
    0 < (lengthsFrom b q).headD 0 := by
  have hn := lengthsFrom_nonempty b q
  cases hr : lengthsFrom b q with
  | nil => exact False.elim (hn hr)
  | cons a r => exact lengthsFrom_positive b q a (by simp [hr])

theorem lengthsFrom_replicate_head (b : Bool) (m : Nat) (q : List Bool) :
    (lengthsFrom b (List.replicate m b ++ q)).headD 0 =
      m + (lengthsFrom b q).headD 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hn := lengthsFrom_nonempty b (List.replicate m b ++ q)
    cases he : lengthsFrom b (List.replicate m b ++ q) with
    | nil => exact False.elim (hn he)
    | cons a r => simp [List.replicate_succ, lengthsFrom, he, bump] at ih ⊢; omega

theorem replicate_prefix_le_head (b : Bool) (m : Nat) (q : List Bool) (hm : 0 < m) :
    m ≤ (linearRuns (List.replicate m b ++ q)).headD 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  change k + 1 ≤ (lengthsFrom b (List.replicate k b ++ q)).headD 0
  rw [lengthsFrom_replicate_head]
  have hh := lengthsFrom_head_positive b q
  omega

/-- A block beginning at any cut is contained in one of the circular runs. -/
theorem linear_head_le_circular {q : List Bool} (hq : q ≠ []) :
    ∃ a ∈ circularRuns q, (linearRuns q).headD 0 ≤ a := by
  have hne : linearRuns q ≠ [] := by
    intro he
    have hh := encode_linearRuns q
    rw [he, encode] at hh
    exact hq hh.symm
  cases hr : linearRuns q with
  | nil => exact False.elim (hne hr)
  | cons a r =>
    let b := q.headD false
    have ha := linearRuns_positive q a (by simp [hr])
    have hqword : q = List.replicate a b ++ encode (!b) r := by
      simpa only [hr, encode] using (encode_linearRuns q).symm
    let z := encode (!b) r ++ List.replicate a b
    have hc : circularRuns q = linearRuns z := by
      unfold circularRuns
      rw [hr, List.headD_cons, hqword]
      congr 1
      simpa only [List.length_replicate] using
        List.rotate_append_length_eq (List.replicate a b) (encode (!b) r)
    have hbound : a ≤ (linearRuns z.reverse).headD 0 := by
      simpa only [z, List.reverse_append, List.reverse_replicate] using
        replicate_prefix_le_head b a (encode (!b) r).reverse ha
    have hn' : linearRuns z.reverse ≠ [] := by
      intro he
      simp only [he, List.headD_nil] at hbound
      omega
    refine ⟨(linearRuns z.reverse).headD 0, ?_, ?_⟩
    · rw [hc, linearRuns_reverse]
      have hh : (linearRuns z.reverse).headD 0 ∈ linearRuns z.reverse := by
        cases he : linearRuns z.reverse with
        | nil => exact False.elim (hn' he)
        | cons a r => simp
      simpa only [linearRuns_reverse, List.mem_reverse] using hh
    · simpa only [hr, List.headD_cons] using hbound

def CircularBlock (q : List Bool) (length : Nat) (b : Bool) : Prop :=
  ∃ k tail, q.rotate k = List.replicate length b ++ tail

theorem CircularBlock.of_isRotated {q z : List Bool} {length : Nat} {b : Bool}
    (hrot : List.IsRotated q z) (h : CircularBlock z length b) : CircularBlock q length b := by
  obtain ⟨i, hi⟩ := hrot
  obtain ⟨k, tail, hk⟩ := h
  exact ⟨i + k, tail, by rw [← List.rotate_rotate, hi, hk]⟩

theorem circularBlock_le_run {q : List Bool} {length : Nat} {b : Bool}
    (hq : Nonconstant q) (hlen : 0 < length) (h : CircularBlock q length b) :
    ∃ a ∈ circularRuns q, length ≤ a := by
  obtain ⟨k, tail, hk⟩ := h
  have hne : List.replicate length b ++ tail ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_append, List.length_replicate, List.length_nil] at hh
    omega
  obtain ⟨a, ha, hbound⟩ := linear_head_le_circular hne
  have hp := replicate_prefix_le_head b length tail hlen
  have hrot := circularRuns_isRotated hq ⟨k, hk⟩
  exact ⟨a, hrot.mem_iff.mp ha, hp.trans hbound⟩

theorem run_is_circularBlock {q : List Bool} {a : Nat} (ha : a ∈ circularRuns q) :
    ∃ b, CircularBlock q a b := by
  obtain ⟨pre, post, hr⟩ := List.mem_iff_append.mp ha
  obtain ⟨b, hb⟩ := circular_encoding_rotated q
  let c := phase b pre.length
  have hword : encode b (circularRuns q) = encode b pre ++
      (List.replicate a c ++ encode (!c) post) := by
    rw [hr, encode_append]
    rfl
  have hblock : CircularBlock (encode b (circularRuns q)) a c := by
    refine ⟨(encode b pre).length, encode (!c) post ++ encode b pre, ?_⟩
    rw [hword]
    simpa only [List.append_assoc] using
      List.rotate_append_length_eq (encode b pre) (List.replicate a c ++ encode (!c) post)
  exact ⟨c, hblock.of_isRotated hb.symm⟩

/-- Run height can be characterized without choosing a circular cut. -/
theorem short_iff_no_long_circularBlock {q : List Bool} {w : Nat} (hq : Nonconstant q) :
    CircularRun.Short w (circularRuns q) ↔ ∀ length b, CircularBlock q length b → length ≤ w := by
  constructor
  · intro hs length b hb
    by_cases hl : length = 0
    · omega
    · obtain ⟨a, ha, hla⟩ := circularBlock_le_run hq (by omega) hb
      exact hla.trans (hs a ha)
  · intro hs a ha
    obtain ⟨b, hb⟩ := run_is_circularBlock ha
    exact hs a b hb

end OddCycle.CircularWord

namespace OddCycle.CircularRun

theorem Reach.of_isRotated {w : Nat} {r s : List Nat} (h : List.IsRotated r s) : Reach w r s := by
  obtain ⟨k, rfl⟩ := h
  rw [List.rotate_eq_drop_append_take_mod]
  have hh := Step.rotate (w := w) (r.take (k % r.length)) (r.drop (k % r.length))
  simpa only [List.take_append_drop] using Relation.ReflTransGen.single hh

theorem terminal_isRotated_iff {w : Nat} {r s : List Nat} (h : List.IsRotated r s) :
    Terminal w r ↔ Terminal w s := by
  exact ⟨fun ht => ht.of_reach (Reach.of_isRotated h),
    fun ht => ht.of_reach (Reach.of_isRotated h.symm)⟩

end OddCycle.CircularRun
