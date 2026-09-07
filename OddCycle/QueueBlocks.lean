import OddCycle.CycleArcBlocks

/-! Small order lemmas for constructing explicit linear extensions by blocks. -/

namespace OddCycle

theorem pair_sublist_of_before {q : Queue} {a b : Nat} (hq : q.Nodup) (ha : a ∈ q) (hb : b ∈ q)
    (h : q.idxOf a < q.idxOf b) : [a, b].Sublist q := by
  apply (sublist_iff_chain_before hq (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> assumption)).mpr
  simpa using h

theorem pair_sublist_between {a b : Nat} {left right : Queue} (ha : a ∈ left) (hb : b ∈ right) :
    [a, b].Sublist (left ++ right) :=
  (List.singleton_sublist.mpr ha).append (List.singleton_sublist.mpr hb)

theorem pair_sublist_filter {q : Queue} {a b : Nat} (p : Nat → Bool)
    (h : [a, b].Sublist q) (ha : p a = true) (hb : p b = true) : [a, b].Sublist (q.filter p) := by
  simpa only [List.filter_cons, ha, hb, if_true, List.filter_nil] using h.filter p

theorem pair_sublist_range {start count i : Nat} (hi : start ≤ i) (hj : i + 1 < start + count) :
    [i, i + 1].Sublist (List.range' start count) := by
  have hsub := (List.take_sublist 2 ((List.range' start count).drop (i - start))).trans
    (List.drop_sublist (i - start) (List.range' start count))
  rw [List.drop_range'] at hsub
  have hlen : 2 ≤ count - (i - start) := by omega
  rw [List.take_range'_of_length_ge hlen] at hsub
  have he : start + (i - start) = i := by omega
  simpa only [mul_one, he, List.range'_succ, List.range'_zero, List.cons_sublist_cons,
    List.nil_sublist] using hsub

theorem pair_sublist_reverse_range {start count i : Nat} (hi : start ≤ i) (hj : i + 1 < start + count) :
    [i + 1, i].Sublist (List.range' start count).reverse := by
  simpa using (pair_sublist_range hi hj).reverse

theorem mem_range_interval {start count i : Nat} : i ∈ List.range' start count ↔ start ≤ i ∧ i < start + count := by
  rw [List.mem_range']
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨hi, hj⟩
    exact ⟨i - start, by omega, by omega⟩

theorem sublist_in_block (pre block post : Queue) : block.Sublist (pre ++ block ++ post) := by
  simpa only [List.append_assoc] using
    (List.sublist_append_left block post).trans (List.sublist_append_right pre (block ++ post))

theorem pair_across_blocks (pre left middle right post : Queue) {a b : Nat}
    (ha : a ∈ left) (hb : b ∈ right) : [a, b].Sublist (pre ++ left ++ middle ++ right ++ post) := by
  have hp := pair_sublist_between ha (List.mem_append_right middle hb)
  have hp' : [a, b].Sublist (left ++ middle ++ right) := by simpa only [List.append_assoc] using hp
  simpa only [List.append_assoc] using hp'.trans (sublist_in_block pre (left ++ middle ++ right) post)

theorem orientation_eq_of_edge_pairs {n : Nat} {s : State} {q : List Bool}
    (hs : Valid n s) (hlen : q.length = n)
    (hp : ∀ i (hi : i < n), (if q[i]'(by omega) then [i, (i + 1) % n] else [(i + 1) % n, i]).Sublist (placement s)) :
    orientation n s = q := by
  apply List.ext_getElem
  · simpa only [orientation_length] using hlen.symm
  · intro i hi hj
    have hin : i < n := by simpa only [orientation_length] using hi
    have hh := hp i hin
    rw [orientation_getElem hin]
    cases hb : q[i] with
    | true =>
      have hpair : [i, (i + 1) % n].Sublist (placement s) := by simpa only [hb, if_true] using hh
      exact decide_eq_true (before_of_pair_sublist hs.placement_nodup hpair)
    | false =>
      have hpair : [(i + 1) % n, i].Sublist (placement s) := by simpa only [hb, Bool.false_eq_true, if_false] using hh
      have hbefore := before_of_pair_sublist hs.placement_nodup hpair
      exact decide_eq_false (Nat.not_lt_of_ge hbefore.le)

end OddCycle
