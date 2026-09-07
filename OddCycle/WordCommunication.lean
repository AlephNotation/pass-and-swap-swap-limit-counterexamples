import OddCycle.Reachability
import OddCycle.CycleCoordinates

/-! Linear extensions communicate through adjacent incompatible exchanges.
The argument works for any symmetric swapping graph. -/

namespace OddCycle

inductive WordSwap (adj : Nat → Nat → Bool) : Queue → Queue → Prop
  | swap (p q : Queue) (x y : Nat) (h : adj x y = false) :
      WordSwap adj (p ++ x :: y :: q) (p ++ y :: x :: q)

abbrev WordReachable (adj : Nat → Nat → Bool) := Relation.ReflTransGen (WordSwap adj)

theorem WordReachable.prepend {adj : Nat → Nat → Bool} {q r : Queue}
    (h : WordReachable adj q r) (p : Queue) : WordReachable adj (p ++ q) (p ++ r) := by
  apply Relation.ReflTransGen.lift (p ++ ·) ?_ h
  intro a b hab
  cases hab with
  | swap pre post x y hxy => simpa [List.append_assoc] using WordSwap.swap (p ++ pre) post x y hxy

theorem WordReachable.edgeEquiv {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) {q r : Queue} (h : WordReachable adj q r) :
    EdgeEquiv adj q r := by
  induction h with
  | refl => exact EdgeEquiv.refl _ _
  | tail _ hstep ih =>
    cases hstep with
    | swap pre post x y hxy => exact ih.trans ((edgeEquiv_swap hsym hxy post).append_left pre)

theorem WordReachable.realize {adj : Nat → Nat → Bool} {q r : Queue}
    (h : WordReachable adj q r) (budget : Nat) : EventReachable adj budget (q, []) (r, []) := by
  apply Relation.ReflTransGen.lift' (fun q => (q, [])) ?_ h
  intro a b hab
  cases hab with
  | swap pre post x y hxy => exact reachable_swap hxy pre post

theorem word_move_left {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) (p q : Queue) (x : Nat)
    (h : ∀ a ∈ p, adj x a = false) : WordReachable adj (p ++ x :: q) (x :: (p ++ q)) := by
  induction p with
  | nil => exact .refl
  | cons a p ih =>
    have hh := (ih (fun b hb => h b (by simp [hb]))).prepend [a]
    have ha : adj a x = false := (hsym a x).trans (h a (by simp))
    exact hh.trans (Relation.ReflTransGen.single (WordSwap.swap [] (p ++ q) a x ha))

/-- Lists with the same distinct population and the same order on graph
edges differ by a sequence of adjacent incompatible exchanges. -/
theorem word_reachable_of_before {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) {q r : Queue}
    (hq : q.Nodup) (hperm : q.Perm r)
    (hbefore : ∀ a ∈ q, ∀ b ∈ q, adj a b = true →
      (q.idxOf a < q.idxOf b ↔ r.idxOf a < r.idxOf b)) :
    WordReachable adj q r := by
  induction r generalizing q with
  | nil =>
    have : q = [] := List.perm_nil.mp hperm
    subst q
    exact .refl
  | cons x r ih =>
    have hx : x ∈ q := hperm.mem_iff.mpr (by simp)
    obtain ⟨p, tail, rfl⟩ := List.mem_iff_append.mp hx
    have hm : (p ++ x :: tail).Perm (x :: (p ++ tail)) := List.perm_middle
    have hnew : (x :: (p ++ tail)).Nodup := hm.nodup_iff.mp hq
    have hnot := (List.nodup_cons.mp hnew).1
    have hxp : x ∉ p := fun hx => hnot (List.mem_append_left _ hx)
    have hfree : ∀ a ∈ p, adj x a = false := by
      intro a ha
      by_cases hadj : adj x a = true
      · have hax : a ≠ x := fun heq => hxp (heq ▸ ha)
        have hleft : (p ++ x :: tail).idxOf a < (p ++ x :: tail).idxOf x := by
          simp only [List.idxOf_append, if_pos ha, if_neg hxp, List.idxOf_cons_self, Nat.zero_add]
          exact List.idxOf_lt_length_of_mem ha
        have hright : (x :: r).idxOf x < (x :: r).idxOf a := by simp [Ne.symm hax]
        have hh := (hbefore x (by simp) a (List.mem_append_left _ ha) hadj).mpr hright
        omega
      · exact Bool.eq_false_iff.mpr hadj
    have hmove := word_move_left hsym p tail x hfree
    have he := hmove.edgeEquiv hsym
    have ht : (p ++ tail).Perm r := (hm.symm.trans hperm).cons_inv
    have htail : ∀ a ∈ p ++ tail, ∀ b ∈ p ++ tail, adj a b = true →
        ((p ++ tail).idxOf a < (p ++ tail).idxOf b ↔ r.idxOf a < r.idxOf b) := by
      intro a ha b hb hab
      have ha' : a ≠ x := fun heq => hnot (heq ▸ ha)
      have hb' : b ≠ x := fun heq => hnot (heq ▸ hb)
      have hma : a ∈ p ++ x :: tail := hm.mem_iff.mpr (List.mem_cons_of_mem _ ha)
      have hmb : b ∈ p ++ x :: tail := hm.mem_iff.mpr (List.mem_cons_of_mem _ hb)
      have hh := (he.before_iff hab).symm.trans (hbefore a hma b hmb hab)
      simpa [List.idxOf_cons, Ne.symm ha', Ne.symm hb'] using hh
    exact hmove.trans ((ih (List.nodup_cons.mp hnew).2 ht htail).prepend [x])

theorem reachable_of_orientation_eq {n budget : Nat} {s t : State}
    (hs : Valid n s) (ht : Valid n t) (hori : orientation n s = orientation n t) :
    EventReachable (cycleAdjacent n) budget s t := by
  have hp := hs.placement_perm.trans ht.placement_perm.symm
  have hwords : WordReachable (cycleAdjacent n) (placement s) (placement t) := by
    apply word_reachable_of_before (cycleAdjacent_symm n) hs.placement_nodup hp
    intro a ha b hb hab
    exact orientation_before_iff hs ht hori (hs.placement_mem.mp ha) (hs.placement_mem.mp hb) hab
  exact (gather_reachable _ budget s).1.trans
    ((hwords.realize budget).trans (gather_reachable _ budget t).2)

end OddCycle
