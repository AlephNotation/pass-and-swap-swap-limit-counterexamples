import OddCycle.OrientationQuotient
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
The circular-composition rewrite system used in the cycle classification.
Rotation changes the selected first run, boundary moves transfer one edge,
and an interior flip splits one run into three. The theorem in this file
classifies terminal components of this rewrite system for arbitrary lengths.
Identification with binary orientations and operational queue transitions is
deliberately not built into the definition of a terminal component.
-/

namespace OddCycle.CircularRun

def Short (w : Nat) (r : List Nat) : Prop := ∀ a ∈ r, a ≤ w

/-- All runs are at least full and there is exactly one edge of excess. -/
def Exceptional (w : Nat) (r : List Nat) : Prop :=
  (∀ a ∈ r, w ≤ a) ∧ r.sum = w * r.length + 1

def deficit (w : Nat) (r : List Nat) : Nat := (r.map (w - ·)).sum

inductive Step (w : Nat) : List Nat → List Nat → Prop
  | rotate (p q : List Nat) : Step w (p ++ q) (q ++ p)
  | give (p q : List Nat) (a b : Nat) (ha : w ≤ a) :
      Step w (p ++ (a + 1) :: b :: q) (p ++ a :: (b + 1) :: q)
  | take (p q : List Nat) (a b : Nat) (hb : w ≤ b) :
      Step w (p ++ a :: (b + 1) :: q) (p ++ (a + 1) :: b :: q)
  | split (p q : List Nat) (a b : Nat) (ha : 0 < a) (hb : 0 < b)
      (hbudget : w ≤ a ∨ w ≤ b) :
      Step w (p ++ (a + 1 + b) :: q) (p ++ a :: 1 :: b :: q)

abbrev Reach (w : Nat) := Relation.ReflTransGen (Step w)
abbrev Terminal (w : Nat) := ReachabilityQuotient.Terminal (Step w)

theorem Step.sum_eq {w : Nat} {r s : List Nat} (h : Step w r s) : r.sum = s.sum := by
  cases h <;> simp only [List.sum_append, List.sum_cons] <;> omega

theorem Step.length_le {w : Nat} {r s : List Nat} (h : Step w r s) : r.length ≤ s.length := by
  cases h <;> simp only [List.length_append, List.length_cons] <;> omega

theorem Reach.length_le {w : Nat} {r s : List Nat} (h : Reach w r s) : r.length ≤ s.length := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.length_le

theorem Step.deficit_le {w : Nat} {r s : List Nat} (h : Step w r s)
    (hlen : r.length = s.length) : deficit w s ≤ deficit w r := by
  cases h with
  | rotate p q => simp [deficit, Nat.add_comm]
  | give p q a b ha =>
    simp only [deficit, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    omega
  | take p q a b hb =>
    simp only [deficit, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    omega
  | split p q a b ha hb hbudget =>
    simp only [List.length_append, List.length_cons] at hlen
    omega

theorem Reach.deficit_le {w : Nat} {r s : List Nat} (h : Reach w r s)
    (hlen : r.length = s.length) : deficit w s ≤ deficit w r := by
  induction h with
  | refl => exact le_rfl
  | @tail s t hprev hstep ih =>
    have hst : s.length = t.length := by
      have := Reach.length_le hprev
      have := hstep.length_le
      omega
    exact (hstep.deficit_le hst).trans (ih (hlen.trans hst.symm))

theorem Terminal.of_reach {w : Nat} {r s : List Nat} (hr : Terminal w r)
    (hrs : Reach w r s) : Terminal w s := by
  intro t hst
  exact (hr t (hrs.trans hst)).trans hrs

theorem Terminal.of_step {w : Nat} {r s : List Nat} (hr : Terminal w r)
    (hrs : Step w r s) : Terminal w s := hr.of_reach (.single hrs)

theorem terminal_length_bound {w : Nat} (hw : 1 ≤ w) {r : List Nat}
    (hr : Terminal w r) : ∀ a ∈ r, a ≤ w + 1 := by
  intro a ha
  by_contra hn
  obtain ⟨p, q, rfl⟩ := List.mem_iff_append.mp ha
  have he : a = 1 + 1 + (a - 2) := by omega
  have hstep : Step w (p ++ a :: q) (p ++ 1 :: 1 :: (a - 2) :: q) := by
    conv_lhs => rw [he]
    exact .split p q 1 (a - 2) (by omega) (by omega) (Or.inr (by omega))
  have hreturn := Reach.length_le (hr _ (.single hstep))
  simp only [List.length_append, List.length_cons] at hreturn
  omega

theorem sum_ge_full {w : Nat} {r : List Nat} (hr : ∀ a ∈ r, w ≤ a) :
    w * r.length ≤ r.sum := by
  induction r with
  | nil => simp
  | cons a r ih =>
    have ha := hr a (by simp)
    have ht := ih (fun b hb => hr b (by simp [hb]))
    simp only [List.length_cons, List.sum_cons, Nat.mul_succ]
    omega

theorem sum_eq_full {w : Nat} {r : List Nat} (hr : ∀ a ∈ r, a = w) :
    r.sum = w * r.length := by
  induction r with
  | nil => simp
  | cons a r ih =>
    have ha := hr a (by simp)
    have ht := ih (fun b hb => hr b (by simp [hb]))
    simp [ha, ht, Nat.mul_succ, Nat.add_comm]

theorem short_step {w : Nat} {r s : List Nat} (hr : Short w r) (h : Step w r s) :
    Short w s ∧ Step w s r := by
  cases h with
  | rotate p q =>
    exact ⟨fun a ha => hr a (by simpa only [List.mem_append, or_comm] using ha), .rotate q p⟩
  | give p q a b ha => have := hr (a + 1) (by simp); omega
  | take p q a b hb => have := hr (b + 1) (by simp); omega
  | split p q a b ha hb hbudget =>
    have := hr (a + 1 + b) (by simp)
    rcases hbudget with hbudget | hbudget <;> omega

theorem short_terminal {w : Nat} {r : List Nat} (hr : Short w r) : Terminal w r := by
  intro s h
  have hp : Short w s ∧ Reach w s r := by
    induction h with
    | refl => exact ⟨hr, .refl⟩
    | tail _ h ih =>
      have hh := short_step ih.1 h
      exact ⟨hh.1, (Relation.ReflTransGen.single hh.2).trans ih.2⟩
  exact hp.2

theorem exceptional_bound {w : Nat} {r : List Nat} (hr : Exceptional w r) :
    ∀ a ∈ r, a ≤ w + 1 := by
  intro a ha
  obtain ⟨p, q, rfl⟩ := List.mem_iff_append.mp ha
  have hp := sum_ge_full (w := w) (r := p) (fun b hb => hr.1 b (by simp [hb]))
  have hq := sum_ge_full (w := w) (r := q) (fun b hb => hr.1 b (by simp [hb]))
  have hs := hr.2
  simp only [List.sum_append, List.sum_cons, List.length_append, List.length_cons,
    Nat.mul_add, Nat.mul_succ] at hs
  omega

theorem exceptional_step {w : Nat} {r s : List Nat} (hr : Exceptional w r)
    (h : Step w r s) : Exceptional w s ∧ Step w s r := by
  have hsum := h.sum_eq
  cases h with
  | rotate p q =>
    refine ⟨⟨fun a ha => hr.1 a (by simpa only [List.mem_append, or_comm] using ha), ?_⟩,
      .rotate q p⟩
    simpa [List.length_append, Nat.add_comm] using hsum.symm.trans hr.2
  | give p q a b ha =>
    have hb := hr.1 b (by simp)
    refine ⟨⟨?_, ?_⟩, .take p q a b hb⟩
    · intro x hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | rfl | hx
      · exact hr.1 x (by simp [hx])
      · exact ha
      · omega
      · exact hr.1 x (by simp [hx])
    · simpa only [List.length_append, List.length_cons] using hsum.symm.trans hr.2
  | take p q a b hb =>
    have ha := hr.1 a (by simp)
    refine ⟨⟨?_, ?_⟩, .give p q a b ha⟩
    · intro x hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | rfl | hx
      · exact hr.1 x (by simp [hx])
      · omega
      · exact hb
      · exact hr.1 x (by simp [hx])
    · simpa only [List.length_append, List.length_cons] using hsum.symm.trans hr.2
  | split p q a b ha hb hbudget =>
    have hbound := exceptional_bound hr (a + 1 + b) (by simp)
    rcases hbudget with hbudget | hbudget <;> omega

theorem exceptional_terminal {w : Nat} {r : List Nat} (hr : Exceptional w r) :
    Terminal w r := by
  intro s h
  have hp : Exceptional w s ∧ Reach w s r := by
    induction h with
    | refl => exact ⟨hr, .refl⟩
    | tail _ h ih =>
      have hh := exceptional_step ih.1 h
      exact ⟨hh.1, (Relation.ReflTransGen.single hh.2).trans ih.2⟩
  exact hp.2

/-- Move the one extra edge across a consecutive string of full runs. -/
theorem transfer_full (w : Nat) (pre p q : List Nat) (hp : ∀ a ∈ p, a = w) :
    Reach w (pre ++ (w + 1) :: (p ++ q)) (pre ++ p ++ (w + 1) :: q) := by
  induction p generalizing pre with
  | nil => simpa using (Relation.ReflTransGen.refl (r := Step w) (a := pre ++ (w + 1) :: q))
  | cons a p ih =>
    have ha := hp a (by simp)
    subst a
    have hfirst := Step.give (w := w) pre (p ++ q) w w (Nat.le_refl _)
    have htail := ih (pre ++ [w]) (fun a ha => hp a (by simp [ha]))
    exact (Relation.ReflTransGen.single hfirst).trans (by simpa [List.append_assoc] using htail)

theorem first_nonfull {w : Nat} {r : List Nat} (h : ¬ ∀ a ∈ r, a = w) :
    ∃ p b q, r = p ++ b :: q ∧ (∀ a ∈ p, a = w) ∧ b ≠ w := by
  induction r with
  | nil => exact False.elim (h (by simp))
  | cons a r ih =>
    by_cases ha : a = w
    · obtain ⟨p, b, q, hp, hfull, hb⟩ := ih (by
        intro hr; apply h; intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hr x hx)
      refine ⟨a :: p, b, q, by simp [hp], ?_, hb⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact hfull x hx
    · exact ⟨[], a, r, rfl, by simp, ha⟩

theorem terminal_overfull_tail {w : Nat} (hw : 1 ≤ w) {r : List Nat}
    (hr : Terminal w ((w + 1) :: r)) : ∀ a ∈ r, a = w := by
  by_contra hn
  obtain ⟨p, b, q, rfl, hp, hb⟩ := first_nonfull hn
  have ht := hr.of_reach (transfer_full w [] p (b :: q) hp)
  have he := Step.give (w := w) p q w b (Nat.le_refl _)
  have hu := ht.of_step he
  have hbound := terminal_length_bound hw hu (b + 1) (by simp)
  have hlt : b < w := by omega
  have hreturn := ht _ (.single he)
  have hd := Reach.deficit_le hreturn (by simp)
  simp only [deficit, List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hd
  omega

/-- Exact classification for the circular-run rewrite relation. -/
theorem terminal_iff {w : Nat} (hw : 1 ≤ w) (r : List Nat) :
    Terminal w r ↔ Short w r ∨ Exceptional w r := by
  constructor
  · intro hr
    by_cases hs : Short w r
    · exact Or.inl hs
    · right
      have hex : ∃ a ∈ r, w < a := by
        simpa only [Short, not_forall, not_le, exists_prop] using hs
      obtain ⟨a, ha, hatall⟩ := hex
      have habound := terminal_length_bound hw hr a ha
      have heq : a = w + 1 := by omega
      obtain ⟨p, q, rfl⟩ := List.mem_iff_append.mp ha
      subst a
      have hrot := hr.of_step (Step.rotate p ((w + 1) :: q))
      have hf := terminal_overfull_tail hw (by simpa using hrot)
      have hfull : ∀ a ∈ p ++ q, a = w := by
        intro a ha
        exact hf a (by simpa only [List.mem_append, or_comm] using ha)
      refine ⟨?_, ?_⟩
      · intro a ha
        simp only [List.mem_append, List.mem_cons] at ha
        rcases ha with ha | rfl | ha
        · exact (hfull a (List.mem_append_left _ ha)).symm.le
        · omega
        · exact (hfull a (List.mem_append_right _ ha)).symm.le
      · have hp := sum_eq_full (w := w) (r := p) (fun a ha => hfull a (by simp [ha]))
        have hq := sum_eq_full (w := w) (r := q) (fun a ha => hfull a (by simp [ha]))
        simp only [List.sum_append, List.sum_cons, List.length_append, List.length_cons,
          Nat.mul_add, Nat.mul_succ, hp, hq]
        omega
  · rintro (h | h)
    · exact short_terminal h
    · exact exceptional_terminal h

end OddCycle.CircularRun
