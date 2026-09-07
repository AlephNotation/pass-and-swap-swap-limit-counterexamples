import OddCycle.UnlimitedCarry
import OddCycle.Reachability

/-! Reversing an unlimited scan enumerates its predecessors by the initiating
position. The reconstruction is proved against the original completion rule. -/

namespace OddCycle

def reverseInput (adj : Nat → Nat → Bool) (rest : Queue) (departed pos : Nat) : Queue :=
  let back := unlimitedCarry adj departed (rest.drop pos).reverse
  rest.take pos ++ back.2 :: back.1.reverse

theorem reverseInput_length (adj : Nat → Nat → Bool) (rest : Queue) (departed pos : Nat) :
    (reverseInput adj rest departed pos).length = rest.length + 1 := by
  simp only [reverseInput, List.length_append, List.length_cons, List.length_reverse,
    unlimitedCarry_length, List.length_take, List.length_drop]
  omega

theorem reverseInput_complete {adj : Nat → Nat → Bool} (hsym : ∀ a b, adj a b = adj b a)
    (rest : Queue) (departed pos budget : Nat) (hpos : pos ≤ rest.length) (hbudget : rest.length + 1 ≤ budget) :
    complete adj budget (reverseInput adj rest departed pos) pos =
      some (rest, departed, (unlimitedCarry adj departed (rest.drop pos).reverse).2) := by
  let back := unlimitedCarry adj departed (rest.drop pos).reverse
  have hinv : unlimitedCarry adj back.2 back.1.reverse = (rest.drop pos, departed) := by
    simpa only [List.reverse_reverse] using unlimitedCarry_inverse hsym (rest.drop pos).reverse departed
  have hlen : back.1.reverse.length ≤ budget := by
    simp only [List.length_reverse, back, unlimitedCarry_length, List.length_drop]
    omega
  have hcarry : carry adj budget back.2 back.1.reverse = (rest.drop pos, departed) :=
    (carry_eq_unlimited adj back.1.reverse back.2 budget hlen).trans hinv
  have hhead : complete adj budget (back.2 :: back.1.reverse) 0 =
      some (rest.drop pos, departed, back.2) := by simp [complete, hcarry]
  have h := complete_append (rest.take pos) hhead
  simpa only [reverseInput, List.length_take, Nat.min_eq_left hpos, Nat.add_zero, List.take_append_drop] using h

theorem complete_reverseInput {adj : Nat → Nat → Bool} (hsym : ∀ a b, adj a b = adj b a)
    {q rest : Queue} {departed initiating pos budget : Nat} (hbudget : q.length ≤ budget)
    (he : complete adj budget q pos = some (rest, departed, initiating)) :
    q = reverseInput adj rest departed pos ∧
      initiating = (unlimitedCarry adj departed (rest.drop pos).reverse).2 := by
  induction q generalizing rest pos with
  | nil => simp [complete] at he
  | cons x xs ih =>
    cases pos with
    | zero =>
      have hc := carry_eq_unlimited adj xs x budget (by simp only [List.length_cons] at hbudget; omega)
      simp only [complete, hc, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hr, hd, hi⟩ := he
      rw [← hr, ← hd, ← hi]
      simp [reverseInput, unlimitedCarry_inverse hsym xs x]
    | succ pos =>
      cases hcomp : complete adj budget xs pos with
      | none => simp [complete, hcomp] at he
      | some result =>
        obtain ⟨r, d, i⟩ := result
        simp [complete, hcomp] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        have hh := ih (by simp only [List.length_cons] at hbudget; omega) hcomp
        simpa [reverseInput] using And.intro (congrArg (x :: ·) hh.1) hh.2

theorem reverseInput_perm {adj : Nat → Nat → Bool} (rest : Queue) (departed pos : Nat) :
    (reverseInput adj rest departed pos).Perm (rest ++ [departed]) := by
  have hp := unlimitedCarry_population adj (rest.drop pos).reverse departed
  have h := (List.reverse_perm _).trans (hp.trans (List.reverse_perm _).symm)
  have h' := h.append_left (rest.take pos)
  simpa [reverseInput, ← List.append_assoc] using h'

theorem reverseInput_edgeEquiv {adj : Nat → Nat → Bool} (hsym : ∀ a b, adj a b = adj b a)
    (rest : Queue) (departed pos : Nat) :
    EdgeEquiv adj (reverseInput adj rest departed pos) (rest ++ [departed]) := by
  have h := (unlimitedCarry_edgeEquiv hsym (rest.drop pos).reverse departed).reverse.symm
  have h' := h.append_left (rest.take pos)
  simpa [reverseInput, ← List.append_assoc] using h'

theorem reverseInput_ends_departed {adj : Nat → Nat → Bool} (pre : Queue) (last departed pos : Nat)
    (hpos : pos ≤ (pre ++ [last]).length) (hadj : adj departed last = true) :
    ∃ q, reverseInput adj (pre ++ [last]) departed pos = q ++ [departed] := by
  by_cases hp : pos ≤ pre.length
  · simp only [reverseInput, List.drop_append, Nat.sub_eq_zero_of_le hp, List.drop_zero,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, unlimitedCarry, hadj, if_true, List.reverse_cons]
    exact ⟨(pre ++ [last]).take pos ++
      (unlimitedCarry adj last (pre.drop pos).reverse).2 ::
        (unlimitedCarry adj last (pre.drop pos).reverse).1.reverse, by simp [List.append_assoc]⟩
  · have he : pos = (pre ++ [last]).length := by
      simp only [List.length_append, List.length_singleton] at hpos ⊢
      omega
    subst pos
    simp [reverseInput, unlimitedCarry]

end OddCycle
