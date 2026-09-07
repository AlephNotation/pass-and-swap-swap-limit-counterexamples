import OddCycle.BinaryCycleGraph

/-! A cut-independent normal form for a single permitted circular flip. -/

namespace OddCycle.CircularWord

def PrefixFlip (w : Nat) (q z : List Bool) : Prop :=
  ∃ b tail, q = List.replicate (w + 1) b ++ tail ∧
    (z = (!b) :: (List.replicate w b ++ tail) ∨
      z = List.replicate w b ++ (!b) :: tail)

theorem PrefixFlip.linearFlip {w : Nat} {q z : List Bool} (h : PrefixFlip w q z) : LinearFlip w q z := by
  obtain ⟨b, tail, rfl, h⟩ := h
  rcases h with rfl | rfl
  · exact LinearFlip.first [] tail b
  · exact LinearFlip.last [] tail b

theorem LinearFlip.prefix_form {w : Nat} {q z : List Bool} (h : LinearFlip w q z) :
    ∃ k, PrefixFlip w (q.rotate k) (z.rotate k) := by
  cases h with
  | first pre post b =>
    refine ⟨pre.length, b, post ++ pre, ?_, Or.inl ?_⟩
    · simpa only [List.append_assoc] using
        List.rotate_append_length_eq pre (List.replicate (w + 1) b ++ post)
    · simpa only [List.append_assoc, List.cons_append] using
        List.rotate_append_length_eq pre ((!b) :: (List.replicate w b ++ post))
  | last pre post b =>
    refine ⟨pre.length, b, post ++ pre, ?_, Or.inr ?_⟩
    · simpa only [List.append_assoc] using
        List.rotate_append_length_eq pre (List.replicate (w + 1) b ++ post)
    · simpa only [List.append_assoc, List.cons_append] using
        List.rotate_append_length_eq pre (List.replicate w b ++ (!b) :: post)

theorem circularFlip_iff_prefix {w : Nat} {q z : List Bool} :
    CircularFlip w q z ↔ ∃ k, PrefixFlip w (q.rotate k) (z.rotate k) := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨i, hi⟩ := hk.prefix_form
    exact ⟨k + i, by simpa only [List.rotate_rotate] using hi⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk.linearFlip⟩

/-- A single bit is complemented, with both surrounding words fixed. -/
def FlipAt (q z : List Bool) (i : Nat) : Prop :=
  ∃ pre post b, pre.length = i ∧ q = pre ++ b :: post ∧ z = pre ++ (!b) :: post

theorem FlipAt.length_eq {q z : List Bool} {i : Nat} (h : FlipAt q z i) : q.length = z.length := by
  obtain ⟨pre, post, b, _, rfl, rfl⟩ := h
  simp

theorem FlipAt.index_lt {q z : List Bool} {i : Nat} (h : FlipAt q z i) : i < q.length := by
  obtain ⟨pre, post, b, rfl, rfl, rfl⟩ := h
  simp

theorem FlipAt.getElem {q z : List Bool} {i : Nat} (h : FlipAt q z i) (j : Nat) (hj : j < q.length) :
    z[j]'(by simpa only [← h.length_eq] using hj) = if j = i then !q[j] else q[j] := by
  obtain ⟨pre, post, b, rfl, rfl, rfl⟩ := h
  by_cases hlt : j < pre.length
  · have hne : j ≠ pre.length := by omega
    simp [hlt, hne]
  · by_cases he : j = pre.length
    · subst j
      simp
    · have hj' : 0 < j - pre.length := by omega
      simp [List.getElem_append, hlt, he, List.getElem_cons, Nat.ne_of_gt hj']

theorem flipAt_of_getElem {q z : List Bool} {i : Nat} (hlen : q.length = z.length) (hi : i < q.length)
    (h : ∀ j (hj : j < q.length), z[j]'(by simpa only [← hlen] using hj) =
      if j = i then !q[j] else q[j]) : FlipAt q z i := by
  refine ⟨q.take i, q.drop (i + 1), q[i], by simp [Nat.min_eq_left hi.le], ?_, ?_⟩
  · have he := List.take_append_drop (i + 1) q
    rw [List.take_succ_eq_append_getElem hi] at he
    simpa only [List.append_assoc, List.singleton_append] using he.symm
  · apply List.ext_getElem
    · simp [hlen, List.length_drop]
      omega
    · intro j hj hj'
      have hjq : j < q.length := by omega
      rw [h j hjq]
      have hqlen : (q.take i).length = i := by simp [Nat.min_eq_left hi.le]
      by_cases hji : j < i
      · have hne : j ≠ i := by omega
        simp [hqlen, hji, hne]
      · by_cases he : j = i
        · subst j
          simp [hqlen]
        · have hjpos : 0 < j - i := by omega
          simp [List.getElem_append, hqlen, hji, he, List.getElem_cons, Nat.ne_of_gt hjpos]
          congr 1
          omega

theorem FlipAt.unique {q z t : List Bool} {i : Nat} (h : FlipAt q z i) (ht : FlipAt q t i) : z = t := by
  apply List.ext_getElem
  · exact h.length_eq.symm.trans ht.length_eq
  · intro j hj hjt
    have hjq : j < q.length := by simpa only [h.length_eq] using hj
    exact (h.getElem j hjq).trans (ht.getElem j hjq).symm

theorem flipAt_first_prefix {w : Nat} {b : Bool} {q z tail : List Bool}
    (hq : q = List.replicate (w + 1) b ++ tail) (h : FlipAt q z 0) :
    z = (!b) :: (List.replicate w b ++ tail) := by
  apply h.unique
  exact ⟨[], List.replicate w b ++ tail, b, rfl,
    by simpa only [List.replicate_succ, List.cons_append] using hq, rfl⟩

theorem flipAt_last_prefix {w : Nat} {b : Bool} {q z tail : List Bool}
    (hq : q = List.replicate (w + 1) b ++ tail) (h : FlipAt q z w) :
    z = List.replicate w b ++ (!b) :: tail := by
  apply h.unique
  refine ⟨List.replicate w b, tail, b, List.length_replicate, ?_, rfl⟩
  simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using hq

end OddCycle.CircularWord
