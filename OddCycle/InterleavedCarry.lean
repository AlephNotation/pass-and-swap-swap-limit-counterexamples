import OddCycle.Interleavings
import OddCycle.BudgetStability
import Mathlib.Data.List.Chain

/-! Evaluate a replacement chain interleaved with incompatible jobs. -/

namespace OddCycle

theorem carry_skip {adj : Nat → Nat → Bool} (budget job : Nat) (pre tail : Queue)
    (h : ∀ x ∈ pre, adj job x = false) :
    carry adj budget job (pre ++ tail) =
      (pre ++ (carry adj budget job tail).1, (carry adj budget job tail).2) := by
  induction pre with
  | nil => rfl
  | cons x xs ih =>
    by_cases hz : budget = 0
    · subst budget
      cases tail <;> simp [carry]
    · have he := ih (fun y hy => h y (by simp [hy]))
      simp [carry, hz, h x (by simp), he]

theorem carry_interleaved_chain {adj : Nat → Nat → Bool} {replace : Nat → Nat}
    (a b mid tail : Queue) (job extra : Nat)
    (hm : mid ∈ interleavings a b)
    (hchain : (job :: a).IsChain (fun x y => adj x y = true ∧ replace y = x))
    (hskip : ∀ x ∈ job :: a, ∀ y ∈ b, adj x y = false)
    (hfix : ∀ y ∈ b, replace y = y) :
    carry adj (a.length + extra) job (mid ++ tail) =
      (mid.map replace ++ (carry adj extra (a.getLast?.getD job) tail).1,
        (carry adj extra (a.getLast?.getD job) tail).2) := by
  induction a generalizing b mid job with
  | nil =>
    simp only [interleavings, List.mem_singleton] at hm
    subst mid
    have hmap : b.map replace = b := by
      calc
        b.map replace = b.map id := List.map_congr_left hfix
        _ = b := List.map_id b
    simpa [hmap] using carry_skip extra job b tail (hskip job (by simp))
  | cons x xs iha =>
    have hp := List.isChain_cons_cons.mp hchain
    have htail (b' : Queue) (hb' : b'.Sublist b) (m : Queue)
        (hm' : m ∈ interleavings xs b') :
        carry adj (xs.length + extra) x (m ++ tail) =
          (m.map replace ++ (carry adj extra (xs.getLast?.getD x) tail).1,
            (carry adj extra (xs.getLast?.getD x) tail).2) :=
      iha b' m x hm' hp.2
        (fun y hy z hz => hskip y (by simp [hy]) z (hb'.subset hz))
        (fun y hy => hfix y (hb'.subset hy))
    induction b generalizing mid with
    | nil =>
      simp only [interleavings, List.mem_singleton] at hm
      subst mid
      have he := htail [] (List.Sublist.refl _) xs (by cases xs <;> simp [interleavings])
      simp [carry, hp.1.1, hp.1.2,
        show xs.length + 1 + extra - 1 = xs.length + extra by omega, he, List.getLast?_cons]
    | cons y ys ihb =>
      rw [interleavings, List.mem_append, List.mem_map, List.mem_map] at hm
      rcases hm with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
      · have he := htail (y :: ys) (List.Sublist.refl _) m hm
        simp [carry, hp.1.1, hp.1.2,
          show xs.length + 1 + extra - 1 = xs.length + extra by omega, he, List.getLast?_cons]
      · have he := ihb m hm (fun x hx z hz => hskip x hx z (by simp [hz]))
          (fun z hz => hfix z (by simp [hz]))
          (fun b' hb' m hm' => htail b' (hb'.cons y) m hm')
        simp only [List.length_cons, List.getLast?_cons, Option.getD_some] at he
        simp [carry, hskip job (by simp) y (by simp), hfix y (by simp), he, List.getLast?_cons]

end OddCycle
