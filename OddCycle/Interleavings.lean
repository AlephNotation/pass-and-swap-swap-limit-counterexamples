import OddCycle.Model
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic

/-! Counting interleavings of two disjoint chains, with exact coverage and
no repetitions. These are candidate enumerations, not state definitions. -/

namespace OddCycle

def interleavings : Queue → Queue → List Queue
  | [], b => [b]
  | a :: as, [] => [a :: as]
  | a :: as, b :: bs =>
      (interleavings as (b :: bs)).map (a :: ·) ++
      (interleavings (a :: as) bs).map (b :: ·)
termination_by a b => a.length + b.length

theorem interleavings_length (a b : Queue) :
    (interleavings a b).length = Nat.choose (a.length + b.length) a.length := by
  induction a generalizing b with
  | nil => simp [interleavings]
  | cons x a iha =>
    induction b with
    | nil => simp [interleavings]
    | cons y b ihb =>
      simp only [interleavings, List.length_append, List.length_map, iha, ihb, List.length_cons]
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.choose_succ_succ (a.length + b.length + 1) a.length).symm

theorem interleavings_swap (a b : Queue) : (interleavings a b).Perm (interleavings b a) := by
  induction a generalizing b with
  | nil => cases b <;> simp [interleavings]
  | cons x xs ihx =>
    induction b with
    | nil => simp [interleavings]
    | cons y ys ihy =>
      rw [interleavings, interleavings]
      exact (((ihx (y :: ys)).map (x :: ·)).append (ihy.map (y :: ·))).trans List.perm_append_comm

theorem sublist_head_eq {x y : Nat} {a q : Queue} (hq : (y :: q).Nodup)
    (h : (x :: a).Sublist (y :: q)) (hy : y ∈ x :: a) : x = y := by
  rcases List.sublist_cons_iff.mp h with h | ⟨r, heq, _⟩
  · exact False.elim ((List.nodup_cons.mp hq).1 (h.subset hy))
  · exact (List.cons.inj heq).1

theorem sublist_of_not_mem_head {x : Nat} {a q : Queue}
    (hx : x ∉ a) (h : a.Sublist (x :: q)) : a.Sublist q := by
  rcases List.sublist_cons_iff.mp h with h | ⟨r, rfl, _⟩
  · exact h
  · exact False.elim (hx (by simp))

theorem mem_interleavings_iff {a b q : Queue} (hab : (a ++ b).Nodup) :
    q ∈ interleavings a b ↔ q.Perm (a ++ b) ∧ a.Sublist q ∧ b.Sublist q := by
  induction a generalizing b q with
  | nil =>
    simp only [interleavings, List.mem_singleton, List.nil_append, List.nil_sublist, true_and]
    constructor
    · rintro rfl; exact ⟨.refl _, .refl _⟩
    · rintro ⟨hp, hs⟩; exact (hs.eq_of_length hp.length_eq.symm).symm
  | cons x a iha =>
    induction b generalizing q with
    | nil =>
      simp only [interleavings, List.mem_singleton, List.append_nil, List.nil_sublist, and_true]
      constructor
      · rintro rfl; exact ⟨.refl _, .refl _⟩
      · rintro ⟨hp, hs⟩; exact (hs.eq_of_length hp.length_eq.symm).symm
    | cons y b ihb =>
      have hleft : (a ++ y :: b).Nodup := (List.nodup_cons.mp hab).2
      have hright : ((x :: a) ++ b).Nodup :=
        (List.nodup_cons.mp (List.perm_middle.nodup_iff.mp hab)).2
      rw [interleavings, List.mem_append, List.mem_map, List.mem_map]
      constructor
      · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
        · obtain ⟨hp, ha, hb⟩ := (iha hleft).mp hr
          exact ⟨hp.cons x, ha.cons₂ x, hb.cons x⟩
        · obtain ⟨hp, ha, hb⟩ := (ihb hright).mp hr
          exact ⟨(hp.cons y).trans List.perm_middle.symm, ha.cons y, hb.cons₂ y⟩
      · rintro ⟨hp, ha, hb⟩
        cases q with
        | nil => simp at ha
        | cons z q =>
          have hq := hp.nodup_iff.mpr hab
          have hz := hp.mem_iff.mp (List.mem_cons_self : z ∈ z :: q)
          rcases List.mem_append.mp hz with hza | hzb
          · have heq := sublist_head_eq hq ha hza
            subst z
            have hxb : x ∉ y :: b := fun hh =>
              (List.nodup_cons.mp hab).1 (List.mem_append_right _ hh)
            exact Or.inl ⟨q, (iha hleft).mpr
              ⟨hp.cons_inv, List.cons_sublist_cons.mp ha, sublist_of_not_mem_head hxb hb⟩, rfl⟩
          · have heq := sublist_head_eq hq hb hzb
            subst z
            have hya : y ∉ x :: a := fun hh =>
              (List.nodup_cons.mp (List.perm_middle.nodup_iff.mp hab)).1 (List.mem_append_left _ hh)
            exact Or.inr ⟨q, (ihb hright).mpr
              ⟨(hp.trans List.perm_middle).cons_inv, sublist_of_not_mem_head hya ha,
                List.cons_sublist_cons.mp hb⟩, rfl⟩

theorem interleavings_nodup {a b : Queue} (hab : (a ++ b).Nodup) :
    (interleavings a b).Nodup := by
  induction a generalizing b with
  | nil => simp [interleavings]
  | cons x a iha =>
    induction b with
    | nil => simp [interleavings]
    | cons y b ihb =>
      have hleft : (a ++ y :: b).Nodup := (List.nodup_cons.mp hab).2
      have hright : ((x :: a) ++ b).Nodup :=
        (List.nodup_cons.mp (List.perm_middle.nodup_iff.mp hab)).2
      have hxy : x ≠ y := fun heq =>
        (List.nodup_cons.mp hab).1 (List.mem_append_right _ (by simp [heq]))
      rw [interleavings, List.nodup_append]
      refine ⟨(iha hleft).map (fun _ _ h => (List.cons.inj h).2),
        (ihb hright).map (fun _ _ h => (List.cons.inj h).2), ?_⟩
      intro q hq q' hq' hqq'
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
      obtain ⟨s, _, heq⟩ := List.mem_map.mp hq'
      exact hxy (List.cons.inj (hqq'.trans heq.symm)).1

theorem common_head_of_cover {u : Nat} {a b q : Queue} (hq : q.Nodup)
    (ha : (u :: a).Sublist q) (hb : (u :: b).Sublist q)
    (hc : ∀ x ∈ q, x ∈ u :: a ∨ x ∈ u :: b) : ∃ rest, q = u :: rest := by
  cases q with
  | nil => simp at ha
  | cons x q =>
    rcases hc x (by simp) with hx | hx
    · exact ⟨q, by rw [sublist_head_eq hq ha hx]⟩
    · exact ⟨q, by rw [sublist_head_eq hq hb hx]⟩

/-- Two covering chains with shared endpoints force those endpoints to be
first and last. Their interiors are precisely a disjoint interleaving. -/
theorem bookended_interleavings {u v : Nat} {a b q : Queue}
    (hn : (u :: (a ++ b) ++ [v]).Nodup) (hp : q.Perm (u :: (a ++ b) ++ [v]))
    (ha : (u :: a ++ [v]).Sublist q) (hb : (u :: b ++ [v]).Sublist q) :
    ∃ mid ∈ interleavings a b, q = u :: mid ++ [v] := by
  have hq := hp.nodup_iff.mpr hn
  have hc (x : Nat) (hx : x ∈ q) : x ∈ u :: a ++ [v] ∨ x ∈ u :: b ++ [v] := by
    have hh := hp.mem_iff.mp hx
    simp only [List.mem_cons, List.mem_append] at hh ⊢
    tauto
  obtain ⟨rest, rfl⟩ := common_head_of_cover hq ha hb hc
  have hrevA : (v :: (a.reverse ++ [u])).Sublist (u :: rest).reverse := by
    simpa using ha.reverse
  have hrevB : (v :: (b.reverse ++ [u])).Sublist (u :: rest).reverse := by
    simpa using hb.reverse
  have hrevC (x : Nat) (hx : x ∈ (u :: rest).reverse) :
      x ∈ v :: (a.reverse ++ [u]) ∨ x ∈ v :: (b.reverse ++ [u]) := by
    have hh := hc x (List.mem_reverse.mp hx)
    simp only [List.mem_cons, List.mem_append, List.mem_reverse] at hh ⊢
    tauto
  have hqn : (u :: rest).reverse.Nodup := by simpa only [List.nodup_reverse] using hq
  obtain ⟨back, heq⟩ := common_head_of_cover (q := (u :: rest).reverse) hqn hrevA hrevB hrevC
  have hback : u :: rest = back.reverse ++ [v] := by
    simpa using congrArg List.reverse heq
  cases hm : back.reverse with
  | nil =>
    have hl := hp.length_eq
    simp only [hm, List.nil_append, List.cons.injEq] at hback
    obtain ⟨rfl, rfl⟩ := hback
    simp at hl
  | cons first mid =>
    simp only [hm, List.cons_append, List.cons.injEq] at hback
    obtain ⟨rfl, rfl⟩ := hback
    have hab : (a ++ b).Nodup :=
      (List.nodup_append.mp (List.nodup_cons.mp hn).2).1
    refine ⟨mid, (mem_interleavings_iff hab).mpr ⟨?_, ?_, ?_⟩, rfl⟩
    · exact (List.perm_append_right_iff [v]).mp hp.cons_inv
    · simpa using ha
    · simpa using hb

end OddCycle
