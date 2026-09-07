import OddCycle.CircularRunDynamics
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.Ring.Parity

/-! Executable run extraction and alternating-block encodings. -/

namespace OddCycle.CircularWord

def phase (b : Bool) (k : Nat) : Bool := if k % 2 = 0 then b else !b

@[simp] theorem phase_zero (b : Bool) : phase b 0 = b := by simp [phase]

theorem phase_succ (b : Bool) (k : Nat) : phase b (k + 1) = phase (!b) k := by
  have hk := Nat.mod_lt k (by omega : 0 < 2)
  have hk' := Nat.mod_lt (k + 1) (by omega : 0 < 2)
  simp only [phase]
  split_ifs <;> simp_all <;> omega

def encode (b : Bool) : List Nat → List Bool
  | [] => []
  | a :: r => List.replicate a b ++ encode (!b) r

theorem encode_length (b : Bool) (r : List Nat) : (encode b r).length = r.sum := by
  induction r generalizing b with
  | nil => rfl
  | cons a r ih => simp [encode, ih]

theorem encode_append (b : Bool) (p q : List Nat) :
    encode b (p ++ q) = encode b p ++ encode (phase b p.length) q := by
  induction p generalizing b with
  | nil => simp [encode]
  | cons a p ih => simp [encode, ih, phase_succ, List.append_assoc]

def bump : List Nat → List Nat
  | [] => [1]
  | a :: r => (a + 1) :: r

def lengthsFrom (b : Bool) : List Bool → List Nat
  | [] => [1]
  | c :: q => if b = c then bump (lengthsFrom c q) else 1 :: lengthsFrom c q

def linearRuns : List Bool → List Nat
  | [] => []
  | b :: q => lengthsFrom b q

theorem lengthsFrom_nonempty (b : Bool) (q : List Bool) : lengthsFrom b q ≠ [] := by
  cases q with
  | nil => simp [lengthsFrom]
  | cons c q =>
    simp only [lengthsFrom]
    split_ifs
    · cases lengthsFrom c q <;> simp [bump]
    · simp

theorem lengthsFrom_positive (b : Bool) (q : List Bool) : ∀ a ∈ lengthsFrom b q, 0 < a := by
  induction q generalizing b with
  | nil => simp [lengthsFrom]
  | cons c q ih =>
    by_cases he : b = c
    · simp only [lengthsFrom, if_pos he]
      cases hr : lengthsFrom c q with
      | nil => simp [bump]
      | cons a r =>
        intro x hx
        simp only [bump, List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact ih c x (by simp [hr, hx])
    · intro a ha
      simp only [lengthsFrom, if_neg he, List.mem_cons] at ha
      rcases ha with rfl | ha
      · omega
      · exact ih c a ha

theorem encode_bump (b : Bool) {r : List Nat} (hr : r ≠ []) :
    encode b (bump r) = b :: encode b r := by
  cases r with
  | nil => exact False.elim (hr rfl)
  | cons a r => simp [encode, bump, List.replicate_succ]

theorem encode_lengthsFrom (b : Bool) (q : List Bool) :
    encode b (lengthsFrom b q) = b :: q := by
  induction q generalizing b with
  | nil => simp [lengthsFrom, encode]
  | cons c q ih =>
    by_cases he : b = c
    · subst c
      simp [lengthsFrom, encode_bump b (lengthsFrom_nonempty b q), ih]
    · have hb : (!b) = c := by cases b <;> cases c <;> simp_all
      simp [lengthsFrom, he, encode, hb, ih]

theorem linearRuns_sum (q : List Bool) : (linearRuns q).sum = q.length := by
  cases q with
  | nil => rfl
  | cons b q =>
    have h := congrArg List.length (encode_lengthsFrom b q)
    simpa only [linearRuns, encode_length] using h

theorem linearRuns_positive (q : List Bool) : ∀ a ∈ linearRuns q, 0 < a := by
  cases q with
  | nil => simp [linearRuns]
  | cons b q => exact lengthsFrom_positive b q

theorem encode_linearRuns (q : List Bool) : encode (q.headD false) (linearRuns q) = q := by
  cases q with
  | nil => rfl
  | cons b q => exact encode_lengthsFrom b q

def Nonconstant (q : List Bool) : Prop := ∃ a ∈ q, ∃ b ∈ q, a ≠ b

theorem not_nonconstant_replicate (n : Nat) (b : Bool) : ¬ Nonconstant (List.replicate n b) := by
  rintro ⟨a, ha, c, hc, hne⟩
  simp only [List.mem_replicate] at ha hc
  exact hne (ha.2.trans hc.2.symm)

theorem nonconstant_two_runs {q : List Bool} (hq : Nonconstant q) :
    ∃ a c r, linearRuns q = a :: c :: r := by
  have he := encode_linearRuns q
  cases hr : linearRuns q with
  | nil =>
    rw [hr, encode] at he
    subst q
    simp [Nonconstant] at hq
  | cons a r =>
    cases r with
    | nil =>
      have hrep : q = List.replicate a (q.headD false) := by simpa [hr, encode] using he.symm
      exact False.elim (not_nonconstant_replicate a (q.headD false) (hrep ▸ hq))
    | cons c r => exact ⟨a, c, r, rfl⟩

theorem encode_head {b : Bool} {a : Nat} {r : List Nat} (ha : 0 < a) :
    (encode b (a :: r)).head? = some b := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  simp [encode, List.replicate_succ]

theorem encode_last {b : Bool} {r : List Nat} (hr : r ≠ [])
    (hpos : ∀ a ∈ r, 0 < a) :
    (encode b r).getLast? = some (phase b (r.length - 1)) := by
  induction r generalizing b with
  | nil => exact False.elim (hr rfl)
  | cons a r ih =>
    cases r with
    | nil =>
      have ha := hpos a (by simp)
      obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
      simp [encode, List.getLast?_replicate, phase]
    | cons c r =>
      have htail := ih (by simp) (fun x hx => hpos x (by simp [hx])) (b := !b)
      have hc := hpos c (by simp)
      have hne : encode (!b) (c :: r) ≠ [] := by
        have hh := encode_head (b := !b) (r := r) hc
        intro he; simp [he] at hh
      change (List.replicate a b ++ encode (!b) (c :: r)).getLast? = _
      rw [List.getLast?_append_of_ne_nil _ hne]
      simpa only [List.length_cons, Nat.add_sub_cancel, phase_succ] using htail

/-- Rotate past the first linear block before extracting runs, so a
nonconstant circular word is cut at a genuine boundary even when its old
first and last bits agree. -/
def circularRuns (q : List Bool) : List Nat :=
  linearRuns (q.rotate ((linearRuns q).headD 0))

theorem circularRuns_sum (q : List Bool) : (circularRuns q).sum = q.length := by
  simp [circularRuns, linearRuns_sum]

theorem circularRuns_positive (q : List Bool) : ∀ a ∈ circularRuns q, 0 < a :=
  linearRuns_positive _

theorem rotated_boundary {q : List Bool} (hq : Nonconstant q) :
    (q.rotate ((linearRuns q).headD 0)).head? ≠
      (q.rotate ((linearRuns q).headD 0)).getLast? := by
  obtain ⟨a, c, r, hr⟩ := nonconstant_two_runs hq
  have he := encode_linearRuns q
  have ha := linearRuns_positive q a (by simp [hr])
  have hc := linearRuns_positive q c (by simp [hr])
  let b := q.headD false
  have heq : q = List.replicate a b ++ encode (!b) (c :: r) := by
    simpa only [hr, encode] using he.symm
  have hrot : q.rotate ((linearRuns q).headD 0) = encode (!b) (c :: r) ++ List.replicate a b := by
    rw [hr, List.headD_cons]
    conv_lhs => rw [heq]
    simpa only [List.length_replicate] using
      List.rotate_append_length_eq (List.replicate a b) (encode (!b) (c :: r))
  have hne : encode (!b) (c :: r) ≠ [] := by
    have hh := encode_head (b := !b) (r := r) hc
    intro h; simp [h] at hh
  have hrepl : List.replicate a b ≠ [] := by simp; omega
  rw [hrot, List.head?_append_of_ne_nil _ hne, List.getLast?_append_of_ne_nil _ hrepl,
    encode_head hc]
  simp [List.getLast?_replicate, Nat.ne_of_gt ha]

theorem linearRuns_even_of_boundary {q : List Bool} (hq : q.head? ≠ q.getLast?) :
    Even (linearRuns q).length := by
  have hne : q ≠ [] := by intro h; simp [h] at hq
  cases q with
  | nil => exact False.elim (hne rfl)
  | cons b q =>
    have hr : linearRuns (b :: q) ≠ [] := lengthsFrom_nonempty b q
    have hpos := linearRuns_positive (b :: q)
    have hlast := encode_last (b := b) hr hpos
    have he : encode b (linearRuns (b :: q)) = b :: q := encode_lengthsFrom b q
    rw [he] at hlast
    have hlen : 0 < (linearRuns (b :: q)).length := List.length_pos_iff.mpr hr
    rw [Nat.even_iff]
    by_contra hn
    have hm : ((linearRuns (b :: q)).length - 1) % 2 = 0 := by omega
    simp only [phase, hm, if_true] at hlast
    exact hq (by simpa using hlast.symm)

theorem circularRuns_even {q : List Bool} (hq : Nonconstant q) : Even (circularRuns q).length :=
  linearRuns_even_of_boundary (rotated_boundary hq)

end OddCycle.CircularWord
