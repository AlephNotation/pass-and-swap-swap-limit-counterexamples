import OddCycle.ReplacementCount

/-! An unlimited predecessor is lost upon truncation precisely when its
backward reconstruction makes more replacements than the budget. -/

namespace OddCycle

theorem complete_prefix (adj : Nat → Nat → Bool) (w : Nat) (pre tail : Queue) (job : Nat) :
    complete adj w (pre ++ job :: tail) pre.length =
      some (pre ++ (carry adj w job tail).1, (carry adj w job tail).2, job) := by
  simpa only [Nat.add_zero] using complete_append pre
    (show complete adj w (job :: tail) 0 = some ((carry adj w job tail).1, (carry adj w job tail).2, job) from rfl)

theorem reverseInput_limited_iff {adj : Nat → Nat → Bool} (hsym : ∀ a b, adj a b = adj b a)
    {rest : Queue} {d p w : Nat} (hnd : (rest ++ [d]).Nodup) (hp : p ≤ rest.length) :
    complete adj w (reverseInput adj rest d p) p =
      some (rest, d, (unlimitedCarry adj d (rest.drop p).reverse).2) ↔
      replacementCount adj d (rest.drop p).reverse ≤ w := by
  let back := unlimitedCarry adj d (rest.drop p).reverse
  have hi : unlimitedCarry adj back.2 back.1.reverse = (rest.drop p, d) := by
    simpa only [back, List.reverse_reverse] using unlimitedCarry_inverse hsym (rest.drop p).reverse d
  have hcount : replacementCount adj back.2 back.1.reverse = replacementCount adj d (rest.drop p).reverse :=
    replacementCount_inverse hsym _ _
  have hqnd := (reverseInput_perm (adj := adj) rest d p).nodup_iff.mpr hnd
  have hbnd : (back.2 :: back.1.reverse).Nodup := (List.nodup_append.mp hqnd).2.1
  have hlen : (rest.take p).length = p := by simp [Nat.min_eq_left hp]
  have hc : complete adj w (reverseInput adj rest d p) p =
      some (rest.take p ++ (carry adj w back.2 back.1.reverse).1,
        (carry adj w back.2 back.1.reverse).2, back.2) := by
    simpa only [hlen] using complete_prefix adj w (rest.take p) back.1.reverse back.2
  rw [hc]
  constructor
  · intro he
    have hd := congrArg (Option.map (fun r : Queue × Nat × Nat => r.2.1)) he
    simp only [Option.map_some, Option.some.injEq] at hd
    by_contra h
    have hn := departed_ne_of_count_lt hbnd (show w < replacementCount adj back.2 back.1.reverse by rw [hcount]; omega)
    rw [hi] at hn
    exact hn hd
  · intro h
    have he := carry_eq_unlimited_of_count adj back.1.reverse w back.2 (by rw [hcount]; exact h)
    rw [he, hi, List.take_append_drop]

theorem replacementCount_no_adj {adj : Nat → Nat → Bool} (job : Nat) (q : Queue)
    (h : ∀ x ∈ q, adj job x = false) : replacementCount adj job q = 0 := by
  induction q with
  | nil => rfl
  | cons x xs ih => simp [replacementCount, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem unlimitedCarry_no_adj {adj : Nat → Nat → Bool} (job : Nat) (q : Queue)
    (h : ∀ x ∈ q, adj job x = false) : unlimitedCarry adj job q = (q, job) := by
  have hh := carry_eq_unlimited_of_count adj q 0 job (by rw [replacementCount_no_adj job q h])
  rw [carry_zero] at hh
  exact hh.symm

theorem replacementCount_chain {adj : Nat → Nat → Bool} (f : Nat → Nat) (k count : Nat) (q : Queue)
    (h : ∀ i, k ≤ i → i < k + count → adj (f i) (f (i + 1)) = true) :
    replacementCount adj (f k) ((List.range' (k + 1) count).map f ++ q) =
      count + replacementCount adj (f (k + count)) q := by
  induction count generalizing k with
  | zero => simp
  | succ count ih =>
    have ha := h k (by omega) (by omega)
    have hh := ih (k + 1) (fun i hi hi' => h i (by omega) (by omega))
    simp only [List.range'_succ, List.map_cons, List.cons_append, replacementCount, ha, if_true]
    rw [hh]
    rw [show k + 1 + count = k + (count + 1) by omega]
    omega

theorem unlimitedCarry_chain {adj : Nat → Nat → Bool} (f : Nat → Nat) (k count : Nat)
    (h : ∀ i, k ≤ i → i < k + count → adj (f i) (f (i + 1)) = true) :
    unlimitedCarry adj (f k) ((List.range' (k + 1) count).map f) =
      ((List.range' k count).map f, f (k + count)) := by
  have hc := carry_chain f k count [] h
  simp only [List.append_nil] at hc
  rw [carry_eq_unlimited adj _ _ count (by simp)] at hc
  exact hc

theorem replacementCount_prefix {adj : Nat → Nat → Bool} {q r : Queue} (job : Nat)
    (h : q.IsPrefix r) : replacementCount adj job q ≤ replacementCount adj job r := by
  obtain ⟨tail, rfl⟩ := h
  rw [replacementCount_append]
  omega

theorem backwardCount_antitone (adj : Nat → Nat → Bool) (rest : Queue) (d : Nat) :
    Antitone (fun p => replacementCount adj d (rest.drop p).reverse) := by
  intro p r hpr
  exact replacementCount_prefix d (List.drop_suffix_drop_left rest hpr).reverse

end OddCycle
