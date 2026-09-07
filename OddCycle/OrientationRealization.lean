import OddCycle.CycleArcBlocks
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! An explicit linear extension for every nonconstant cycle orientation.
Clockwise edges increase an integer potential by the number of zero bits;
counterclockwise edges decrease it by the number of one bits. The total
increment around the cycle is zero. Sorting vertices by this potential
therefore realizes every requested edge direction. -/

namespace OddCycle.CircularWord

def increment (q : List Bool) (b : Bool) : Int :=
  if b then (q.count false : Int) else -(q.count true : Int)

def potential (q : List Bool) (i : Nat) : Int := ((q.take i).map (increment q)).sum

theorem signed_sum (q : List Bool) (up down : Int) :
    (q.map (fun b => if b then up else -down)).sum =
      (q.count true : Int) * up - (q.count false : Int) * down := by
  induction q with
  | nil => simp
  | cons b q ih => cases b <;> simp [ih, Int.add_mul] <;> ring

theorem increment_sum (q : List Bool) : (q.map (increment q)).sum = 0 := by
  unfold increment
  rw [signed_sum]
  ring

theorem potential_total (q : List Bool) : potential q q.length = 0 := by
  simp [potential, increment_sum]

theorem potential_zero (q : List Bool) : potential q 0 = 0 := by simp [potential]

theorem potential_succ {q : List Bool} {i : Nat} (hi : i < q.length) :
    potential q (i + 1) = potential q i + increment q q[i] := by
  unfold potential
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
  simp

theorem potential_wrap {q : List Bool} {i : Nat} (hi : i < q.length) :
    potential q ((i + 1) % q.length) = potential q (i + 1) := by
  by_cases h : i + 1 < q.length
  · rw [Nat.mod_eq_of_lt h]
  · have he : i + 1 = q.length := by omega
    rw [he, Nat.mod_self, potential_zero, potential_total]

theorem Nonconstant.count_pos {q : List Bool} (hq : Nonconstant q) (b : Bool) : 0 < q.count b := by
  obtain ⟨a, ha, c, hc, hne⟩ := hq
  apply List.count_pos_iff.mpr
  cases a <;> cases c <;> cases b <;> simp_all

theorem potential_edge {q : List Bool} (hq : Nonconstant q) {i : Nat} (hi : i < q.length) :
    (q[i] = true → potential q i < potential q ((i + 1) % q.length)) ∧
    (q[i] = false → potential q ((i + 1) % q.length) < potential q i) := by
  rw [potential_wrap hi, potential_succ hi]
  have hu : (0 : Int) < (q.count false : Int) := by exact_mod_cast hq.count_pos false
  have hd : (0 : Int) < (q.count true : Int) := by exact_mod_cast hq.count_pos true
  constructor
  · intro h
    rw [increment, h]
    exact lt_add_of_pos_right _ hu
  · intro h
    rw [increment, h]
    change potential q i + -(q.count true : Int) < potential q i
    omega

def realizingWord (q : List Bool) : OddCycle.Queue :=
  (List.range q.length).mergeSort (fun a b => decide (potential q a ≤ potential q b))

theorem realizingWord_perm (q : List Bool) : (realizingWord q).Perm (List.range q.length) :=
  List.mergeSort_perm _ _

theorem realizingWord_sorted (q : List Bool) :
    (realizingWord q).Pairwise (fun a b => potential q a ≤ potential q b) := by
  have hh := List.pairwise_mergeSort (le := fun a b => decide (potential q a ≤ potential q b))
    (by intro a b c; simp only [decide_eq_true_eq]; exact le_trans)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq];
        exact le_total (potential q a) (potential q b)) (List.range q.length)
  simpa only [realizingWord, decide_eq_true_eq] using hh

theorem sorted_before_of_lt {q : List Bool} {a b : Nat} (ha : a < q.length) (hb : b < q.length)
    (h : potential q a < potential q b) : (realizingWord q).idxOf a < (realizingWord q).idxOf b := by
  have hma : a ∈ realizingWord q := (realizingWord_perm q).mem_iff.mpr (List.mem_range.mpr ha)
  have hmb : b ∈ realizingWord q := (realizingWord_perm q).mem_iff.mpr (List.mem_range.mpr hb)
  have hne : a ≠ b := by intro he; subst b; omega
  have hind : (realizingWord q).idxOf a ≠ (realizingWord q).idxOf b :=
    fun he => hne ((List.idxOf_inj hma).mp he)
  by_contra hn
  have hba : (realizingWord q).idxOf b < (realizingWord q).idxOf a := by omega
  have hs := List.pairwise_iff_getElem.mp (realizingWord_sorted q)
    ((realizingWord q).idxOf b) ((realizingWord q).idxOf a)
    (List.idxOf_lt_length_of_mem hmb) (List.idxOf_lt_length_of_mem hma) hba
  have hh : potential q b ≤ potential q a := by simpa using hs
  omega

theorem realizingWord_valid (q : List Bool) : OddCycle.Valid q.length (realizingWord q, []) := by
  simpa only [OddCycle.Valid, List.append_nil] using realizingWord_perm q

theorem realizingWord_orientation {q : List Bool} (hq : Nonconstant q) :
    OddCycle.orientation q.length (realizingWord q, []) = q := by
  apply List.ext_getElem
  · exact OddCycle.orientation_length _ _
  · intro i hi hj
    have hjnext : (i + 1) % q.length < q.length := Nat.mod_lt _ (by omega)
    have hbits := potential_edge hq hj
    rw [OddCycle.orientation_getElem hj]
    cases he : q[i] with
    | false =>
      have hb := sorted_before_of_lt hjnext hj (hbits.2 he)
      simp only [OddCycle.edgeBit, OddCycle.placement, List.reverse_nil, List.append_nil,
        decide_eq_false_iff_not]
      omega
    | true =>
      have hb := sorted_before_of_lt hj hjnext (hbits.1 he)
      simpa only [OddCycle.edgeBit, OddCycle.placement, List.reverse_nil, List.append_nil,
        decide_eq_true_eq] using hb

end OddCycle.CircularWord

namespace OddCycle

/-- Every nonconstant binary cycle word has an actual queue-state
representative, obtained by an explicit sort rather than an acyclicity axiom. -/
theorem orientation_surjective {n : Nat} {q : List Bool} (hlen : q.length = n)
    (hq : CircularWord.Nonconstant q) : ∃ s, Valid n s ∧ orientation n s = q := by
  refine ⟨(CircularWord.realizingWord q, []), ?_, ?_⟩
  · simpa only [hlen] using CircularWord.realizingWord_valid q
  · simpa only [hlen] using CircularWord.realizingWord_orientation hq

end OddCycle
