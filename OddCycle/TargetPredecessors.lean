import OddCycle.TwoFlowBalance
import OddCycle.UnlimitedPredecessors
import OddCycle.IncomingOccurrences
import OddCycle.GeneralClosure

/-! A complete structural description of the target's unlimited predecessors. -/

namespace OddCycle

def firstFlowSource (w : Nat) : State := ([0, 2 * w], w :: flowCore w)
def secondFlowSource (w pos : Nat) : State :=
  ([], reverseInput (cycleAdjacent (2 * w + 1)) (flowQueue w) 0 pos)
def secondFlowInitiating (w pos : Nat) : Nat :=
  (unlimitedCarry (cycleAdjacent (2 * w + 1)) 0 ((flowQueue w).drop pos).reverse).2

theorem flowTarget_valid_balanced {w : Nat} (hw : 2 ≤ w) :
    Valid (2 * w + 1) (flowTarget w) ∧ balanced w (flowTarget w) = true := by
  have htr : transition (cycleAdjacent (2 * w + 1)) w (flowSourceX w) true 0 = some (flowTarget w, w) := by
    simp [transition, flowSourceX, (flowX_complete hw (show w < w + 1 by omega)).1, flowTarget]
  exact ⟨transition_valid (flowSourceX_valid_balanced hw).1 htr,
    balanced_transition hw (flowSourceX_valid_balanced hw).1 (flowSourceX_valid_balanced hw).2 htr⟩

theorem firstFlowSource_valid_balanced {w : Nat} (hw : 2 ≤ w) :
    Valid (2 * w + 1) (firstFlowSource w) ∧ balanced w (firstFlowSource w) = true := by
  have hp : placement (firstFlowSource w) = placement (flowTarget w) := by
    simp [firstFlowSource, flowTarget, flowQueue, placement]
  have ho : orientation (2 * w + 1) (firstFlowSource w) = orientation (2 * w + 1) (flowTarget w) := by
    simp only [orientation, hp]
  refine ⟨?_, balanced_of_orientation_eq ho (flowTarget_valid_balanced hw).2⟩
  rw [valid_iff_placement_valid, hp, ← valid_iff_placement_valid]
  exact (flowTarget_valid_balanced hw).1

theorem secondFlowSource_valid_balanced {w pos : Nat} (hw : 2 ≤ w) :
    Valid (2 * w + 1) (secondFlowSource w pos) ∧ balanced w (secondFlowSource w pos) = true := by
  have hv := (flowTarget_valid_balanced hw).1.exchange
  have hb := balanced_exchange hw (flowTarget_valid_balanced hw).1 (flowTarget_valid_balanced hw).2
  have hp := reverseInput_perm (adj := cycleAdjacent (2 * w + 1)) (flowQueue w) 0 pos
  have hq : Valid (2 * w + 1) (reverseInput (cycleAdjacent (2 * w + 1)) (flowQueue w) 0 pos, []) := by
    exact (by simpa [Valid, flowTarget, exchange] using hp.trans hv)
  have ho : orientation (2 * w + 1) (reverseInput (cycleAdjacent (2 * w + 1)) (flowQueue w) 0 pos, []) =
      orientation (2 * w + 1) (exchange (flowTarget w)) := by
    apply EdgeEquiv.orientation_eq
    simpa [placement, exchange, flowTarget] using reverseInput_edgeEquiv
      (cycleAdjacent_symm (2 * w + 1)) (flowQueue w) 0 pos
  have hqb := balanced_of_orientation_eq ho hb
  exact ⟨hq.exchange, balanced_exchange hw hq hqb⟩

theorem firstFlowSource_transitions (w : Nat) :
    transition (cycleAdjacent (2 * w + 1)) (2 * w + 1) (firstFlowSource w) false 0 = some (flowTarget w, 0) ∧
    transition (cycleAdjacent (2 * w + 1)) (2 * w + 1) (firstFlowSource w) false 1 = some (flowTarget w, 2 * w) := by
  have ha : cycleAdjacent (2 * w + 1) 0 (2 * w) = true := by simp [cycleAdjacent]
  simp [transition, firstFlowSource, complete, carry, ha, flowTarget, flowQueue]

theorem secondFlowSource_transition {w pos : Nat} (hw : 2 ≤ w) (hp : pos ≤ 2 * w) :
    transition (cycleAdjacent (2 * w + 1)) (2 * w + 1) (secondFlowSource w pos) true pos =
      some (flowTarget w, secondFlowInitiating w pos) := by
  have h := reverseInput_complete (cycleAdjacent_symm (2 * w + 1)) (flowQueue w) 0 pos (2 * w + 1)
    (by simpa only [flowQueue_length hw] using hp) (by rw [flowQueue_length hw])
  simp [transition, secondFlowSource, h, flowTarget, secondFlowInitiating]

theorem unlimited_second_incoming {w pos initiating : Nat} {s : State}
    (hv : Valid (2 * w + 1) s)
    (he : transition (cycleAdjacent (2 * w + 1)) (2 * w + 1) s true pos = some (flowTarget w, initiating)) :
    s = secondFlowSource w pos ∧ pos ≤ 2 * w ∧ initiating = secondFlowInitiating w pos := by
  cases hcomp : complete (cycleAdjacent (2 * w + 1)) (2 * w + 1) s.2 pos with
  | none => simp [transition, hcomp] at he
  | some result =>
    obtain ⟨rest, departed, init⟩ := result
    simp [transition, hcomp, flowTarget] at he
    obtain ⟨⟨hc, hr⟩, hi⟩ := he
    have hlen := congrArg List.length hc
    simp only [List.length_append, List.length_singleton] at hlen
    have hempty : s.1 = [] := by simpa using (show s.1.length = 0 by omega)
    have hd : departed = 0 := by simpa [hempty] using hc
    subst rest
    subst departed
    subst init
    have hl := hv.length_eq
    simp only [hempty, List.nil_append, List.length_range] at hl
    have hp := complete_pos_lt hcomp
    have hr := complete_reverseInput (cycleAdjacent_symm (2 * w + 1)) (by omega : s.2.length ≤ 2 * w + 1) hcomp
    exact ⟨Prod.ext hempty hr.1, by omega, hr.2⟩

theorem perm_two {q : Queue} {a b : Nat} (h : q.Perm [a, b]) : q = [a, b] ∨ q = [b, a] := by
  have hlen : q.length = 2 := by simpa using h.length_eq
  cases q with
  | nil => simp at hlen
  | cons x xs =>
    cases xs with
    | nil => simp at hlen
    | cons y ys =>
      have hy : ys = [] := by simpa using (show ys.length = 0 by simpa using hlen)
      subst ys
      have hx : x = a ∨ x = b := by simpa using h.mem_iff.mp (List.mem_cons_self : x ∈ [x, y])
      rcases hx with hxa | hxb
      · have h' : [a, y].Perm [a, b] := by simpa only [hxa] using h
        have he := h'.cons_inv
        have hy : y = b := by simpa using he.mem_iff.mp (List.mem_cons_self : y ∈ [y])
        exact Or.inl (by simp [hxa, hy])
      · have h' : [b, y].Perm [a, b] := by simpa only [hxb] using h
        have he := (h'.trans (List.Perm.swap b a [])).cons_inv
        have hy : y = a := by simpa using he.mem_iff.mp (List.mem_cons_self : y ∈ [y])
        exact Or.inr (by simp [hxb, hy])

theorem unlimited_first_incoming {w pos initiating : Nat} {s : State} (hw : 2 ≤ w)
    (he : transition (cycleAdjacent (2 * w + 1)) (2 * w + 1) s false pos = some (flowTarget w, initiating)) :
    s = firstFlowSource w ∧ ((pos = 0 ∧ initiating = 0) ∨ (pos = 1 ∧ initiating = 2 * w)) := by
  cases hcomp : complete (cycleAdjacent (2 * w + 1)) (2 * w + 1) s.1 pos with
  | none => simp [transition, hcomp] at he
  | some result =>
    obtain ⟨rest, departed, init⟩ := result
    simp [transition, hcomp, flowTarget] at he
    obtain ⟨⟨hr, hd⟩, hi⟩ := he
    have hdep : departed = 2 * w := by
      have hh := congrArg List.getLast? hd
      simpa only [flowQueue, List.getLast?_append, List.getLast?_singleton, Option.or, Option.some.injEq] using hh
    subst departed
    have hsecond : s.2 = w :: flowCore w := by
      simpa only [flowQueue, List.append_cancel_right_eq] using hd
    subst rest
    subst init
    have hp := (complete_population hcomp).symm
    have hcases : s.1 = [0, 2 * w] ∨ s.1 = [2 * w, 0] := perm_two hp
    have hpos := complete_pos_lt hcomp
    have ha : cycleAdjacent (2 * w + 1) 0 (2 * w) = true := by simp [cycleAdjacent]
    have ha' : cycleAdjacent (2 * w + 1) (2 * w) 0 = true := by simpa only [cycleAdjacent_symm] using ha
    rcases hcases with hfirst | hfirst
    · have hpos' : pos = 0 ∨ pos = 1 := by simp only [hfirst, List.length_cons, List.length_nil] at hpos; omega
      refine ⟨Prod.ext hfirst hsecond, ?_⟩
      rcases hpos' with rfl | rfl
      · have hi' : initiating = 0 := by simpa [hfirst, complete, carry, ha, eq_comm] using hcomp
        exact Or.inl ⟨rfl, hi'⟩
      · have hi' : initiating = 2 * w := by simpa [hfirst, complete, carry, eq_comm] using hcomp
        exact Or.inr ⟨rfl, hi'⟩
    · have hpos' : pos = 0 ∨ pos = 1 := by simp only [hfirst, List.length_cons, List.length_nil] at hpos; omega
      rcases hpos' with rfl | rfl <;>
        simp [hfirst, complete, carry, ha', show 2 * w ≠ 0 by omega] at hcomp

end OddCycle
