import OddCycle.CircularRunDynamics
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! Arithmetic and communication of the single-overfull-run parameters. -/

namespace OddCycle.CircularRun

theorem exceptional_iff_one_long {w : Nat} {r : List Nat} :
    Exceptional w r ↔ ∃ p q, r = p ++ (w + 1) :: q ∧ ∀ a ∈ p ++ q, a = w := by
  constructor
  · intro hr
    have hn : ¬ ∀ a ∈ r, a = w := by
      intro h
      have he := sum_eq_full h
      have := hr.2
      omega
    obtain ⟨p, a, q, rfl, hp, ha⟩ := first_nonfull hn
    have hle := exceptional_bound hr a (by simp)
    have hge := hr.1 a (by simp)
    have he : a = w + 1 := by omega
    subst a
    refine ⟨p, q, rfl, ?_⟩
    have hpsum := sum_eq_full hp
    have hqsum : q.sum = w * q.length := by
      have hs := hr.2
      simp only [List.sum_append, List.sum_cons, List.length_append, List.length_cons,
        Nat.mul_add, Nat.mul_succ, hpsum] at hs
      omega
    have hq : ∀ a ∈ q, a = w := by
      intro b hb
      obtain ⟨u, v, rfl⟩ := List.mem_iff_append.mp hb
      have hu := sum_ge_full (w := w) (r := u) (fun a ha => hr.1 a (by simp [ha]))
      have hv := sum_ge_full (w := w) (r := v) (fun a ha => hr.1 a (by simp [ha]))
      have hmin := hr.1 b (by simp)
      simp only [List.sum_append, List.sum_cons, List.length_append, List.length_cons,
        Nat.mul_add, Nat.mul_succ] at hqsum
      omega
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hp a ha
    · exact hq a ha
  · rintro ⟨p, q, rfl, hfull⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      simp only [List.mem_append, List.mem_cons] at ha
      rcases ha with ha | rfl | ha
      · exact (hfull a (by simp [ha])).symm.le
      · omega
      · exact (hfull a (by simp [ha])).symm.le
    · have hp := sum_eq_full (w := w) (r := p) (fun a ha => hfull a (by simp [ha]))
      have hq := sum_eq_full (w := w) (r := q) (fun a ha => hfull a (by simp [ha]))
      simp only [List.sum_append, List.sum_cons, List.length_append, List.length_cons,
        Nat.mul_add, Nat.mul_succ, hp, hq]
      omega

/-- The exceptional length condition follows from the exact run pattern,
not from a finite screen or an assumed congruence characterization. -/
theorem exceptional_cycle_length {n w : Nat} {r : List Nat}
    (hr : Exceptional w r) (hsum : r.sum = n) (heven : Even r.length) :
    ∃ k, 1 ≤ k ∧ n = 2 * k * w + 1 := by
  obtain ⟨k, hk⟩ := heven
  have hne : r ≠ [] := by intro he; simp [Exceptional, he] at hr
  have hlen : 0 < r.length := List.length_pos_iff.mpr hne
  refine ⟨k, by omega, ?_⟩
  rw [← hsum, hr.2, hk]
  ring

end CircularRun

namespace ExceptionalCycle

abbrev Parameter (n : Nat) := ZMod n × Bool

/-- Moving the extra edge to the next run. The reverse neighbor move can be
added without changing the reachability conclusion proved below. -/
def Step (n w : Nat) (s t : Parameter n) : Prop := t = (s.1 + w, !s.2)

abbrev Reach (n w : Nat) := Relation.ReflTransGen (Step n w)

theorem step (n w : Nat) (a : ZMod n) (b : Bool) :
    Reach n w (a, b) (a + w, !b) := .single rfl

theorem two_steps (n w : Nat) (a : ZMod n) (b : Bool) :
    Reach n w (a, b) (a + 2 * w, b) := by
  have h := (step n w a b).trans (step n w (a + w) (!b))
  convert h using 1
  simp only [Bool.not_not]
  congr 1
  ring

theorem even_steps (n w k : Nat) (a : ZMod n) (b : Bool) :
    Reach n w (a, b) (a + 2 * k * w, b) := by
  induction k generalizing a with
  | zero => simpa using (Relation.ReflTransGen.refl (r := Step n w) (a := (a, b)))
  | succ k ih =>
    have h := (two_steps n w a b).trans (ih (a + 2 * w))
    convert h using 1
    push_cast
    congr 1
    ring

theorem backwards_one {n w k : Nat} (hn : n = 2 * k * w + 1)
    (a : ZMod n) (b : Bool) : Reach n w (a, b) (a - 1, b) := by
  have hz : (2 : ZMod n) * k * w + 1 = 0 := by
    calc
      _ = ((2 * k * w + 1 : Nat) : ZMod n) := by push_cast; rfl
      _ = (n : ZMod n) := by rw [hn]
      _ = 0 := ZMod.natCast_self n
  have he : a + 2 * (k : ZMod n) * w = a - 1 := by
    calc
      _ = a + (2 * (k : ZMod n) * w + 1) - 1 := by ring
      _ = a - 1 := by rw [hz]; ring
  simpa only [he] using even_steps n w k a b

theorem backwards {n w k : Nat} (hn : n = 2 * k * w + 1)
    (a : ZMod n) (b : Bool) (m : Nat) : Reach n w (a, b) (a - m, b) := by
  induction m generalizing a with
  | zero => simpa using (Relation.ReflTransGen.refl (r := Step n w) (a := (a, b)))
  | succ m ih =>
    have h := (backwards_one hn a b).trans (ih (a - 1))
    convert h using 1
    push_cast
    congr 1
    ring

/-- All 2n parameters communicate: 2k forward moves translate by minus one
without changing the bit. One further move changes the bit when needed. -/
theorem communication {n w k : Nat} (hn : n = 2 * k * w + 1)
    (s t : Parameter n) : Reach n w s t := by
  have hnpos : 0 < n := by omega
  letI : NeZero n := ⟨by omega⟩
  have same (a c : ZMod n) (b : Bool) : Reach n w (a, b) (c, b) := by
    have h := backwards hn a b (a - c).val
    simpa using h
  obtain ⟨a, b⟩ := s
  obtain ⟨c, d⟩ := t
  by_cases he : b = d
  · subst d; exact same a c b
  · have hb : (!b) = d := by cases b <;> cases d <;> simp_all
    exact (step n w a b).trans (by rw [hb]; exact same (a + w) c d)

theorem parameter_count {n : Nat} [NeZero n] : Fintype.card (Parameter n) = 2 * n := by
  simp [Parameter, Fintype.card_prod, Nat.mul_comm]

end ExceptionalCycle
end OddCycle
