import OddCycle.CyclePathMoves

/-! Simple paths on a cycle have a single geometric direction. -/

namespace OddCycle

def Clockwise (n a b : Nat) : Prop := (a + 1) % n = b

theorem clockwise_iff {n a b : Nat} (ha : a < n) :
    Clockwise n a b ↔ (a + 1 = b ∧ a + 1 < n) ∨ (a + 1 = n ∧ b = 0) := by
  unfold Clockwise
  by_cases h : a + 1 < n
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have hn : a + 1 = n := by omega
    simp [hn, eq_comm]

theorem clockwise_injective {n a b c : Nat} (ha : a < n) (hc : c < n)
    (hab : Clockwise n a b) (hcb : Clockwise n c b) : a = c := by
  have h1 := (clockwise_iff ha).mp hab
  have h2 := (clockwise_iff hc).mp hcb
  omega

theorem cycleAdjacent_clockwise_iff (n a b : Nat) :
    cycleAdjacent n a b = true ↔ Clockwise n a b ∨ Clockwise n b a := by
  simp [cycleAdjacent, Clockwise]

theorem cycle_path_clockwise {n a b : Nat} {tail : Queue}
    (hnd : (a :: b :: tail).Nodup) (hlabels : ∀ x ∈ a :: b :: tail, x < n)
    (hpath : pathEdges (cycleAdjacent n) (a :: b :: tail) = true)
    (hfirst : Clockwise n a b) : (a :: b :: tail).IsChain (Clockwise n) := by
  induction tail generalizing a b with
  | nil => simpa using hfirst
  | cons c tail ih =>
    have hp : cycleAdjacent n a b = true ∧ cycleAdjacent n b c = true ∧
        pathEdges (cycleAdjacent n) (c :: tail) = true := by
      simpa only [pathEdges, Bool.and_eq_true] using hpath
    have hnext : Clockwise n b c := by
      rcases (cycleAdjacent_clockwise_iff n b c).mp hp.2.1 with hh | hh
      · exact hh
      · have he := clockwise_injective (hlabels a (by simp)) (hlabels c (by simp)) hfirst hh
        exact False.elim ((List.nodup_cons.mp hnd).1 (by simp [he]))
    have ht := ih (List.nodup_cons.mp hnd).2
      (fun x hx => hlabels x (List.mem_cons_of_mem _ hx))
      (by simpa only [pathEdges, Bool.and_eq_true] using hp.2) hnext
    exact List.isChain_cons_cons.mpr ⟨hfirst, ht⟩

theorem cycle_path_counterclockwise {n a b : Nat} {tail : Queue}
    (hnd : (a :: b :: tail).Nodup) (hlabels : ∀ x ∈ a :: b :: tail, x < n)
    (hpath : pathEdges (cycleAdjacent n) (a :: b :: tail) = true)
    (hfirst : Clockwise n b a) :
    (a :: b :: tail).IsChain (fun x y => Clockwise n y x) := by
  induction tail generalizing a b with
  | nil => simpa using hfirst
  | cons c tail ih =>
    have hp : cycleAdjacent n a b = true ∧ cycleAdjacent n b c = true ∧
        pathEdges (cycleAdjacent n) (c :: tail) = true := by
      simpa only [pathEdges, Bool.and_eq_true] using hpath
    have hnext : Clockwise n c b := by
      rcases (cycleAdjacent_clockwise_iff n b c).mp hp.2.1 with hh | hh
      · have he : a = c := hfirst.symm.trans hh
        exact False.elim ((List.nodup_cons.mp hnd).1 (by simp [he]))
      · exact hh
    have ht := ih (List.nodup_cons.mp hnd).2
      (fun x hx => hlabels x (List.mem_cons_of_mem _ hx))
      (by simpa only [pathEdges, Bool.and_eq_true] using hp.2) hnext
    exact List.isChain_cons_cons.mpr ⟨hfirst, ht⟩

theorem cycle_path_direction {n : Nat} {p : Queue} (hnd : p.Nodup)
    (hlabels : ∀ x ∈ p, x < n) (hpath : pathEdges (cycleAdjacent n) p = true) :
    p.IsChain (Clockwise n) ∨ p.IsChain (fun a b => Clockwise n b a) := by
  cases p with
  | nil => simp
  | cons a p =>
    cases p with
    | nil => simp
    | cons b tail =>
      have hp : cycleAdjacent n a b = true ∧
          pathEdges (cycleAdjacent n) (b :: tail) = true := by
        simpa only [pathEdges, Bool.and_eq_true] using hpath
      rcases (cycleAdjacent_clockwise_iff n a b).mp hp.1 with hh | hh
      · exact Or.inl (cycle_path_clockwise hnd hlabels hpath hh)
      · exact Or.inr (cycle_path_counterclockwise hnd hlabels hpath hh)

def cycleArc (n start edges : Nat) : Queue :=
  (List.range (edges + 1)).map (fun i => (start + i) % n)

theorem clockwise_chain_getElem {n a : Nat} {tail : Queue} (ha : a < n)
    (hp : (a :: tail).IsChain (Clockwise n)) (i : Nat) (hi : i < (a :: tail).length) :
    (a :: tail)[i] = (a + i) % n := by
  induction i with
  | zero => simpa using (Nat.mod_eq_of_lt ha).symm
  | succ i ih =>
    have hil : i < (a :: tail).length := by omega
    have hh := List.isChain_iff_getElem.mp hp i hi
    change ((a :: tail)[i] + 1) % n = (a :: tail)[i + 1] at hh
    rw [ih hil] at hh
    rw [← hh, Nat.mod_add_mod]
    congr 1

theorem clockwise_chain_eq_arc {n a : Nat} {tail : Queue} (ha : a < n)
    (hp : (a :: tail).IsChain (Clockwise n)) :
    a :: tail = cycleArc n a tail.length := by
  apply List.ext_getElem
  · simp [cycleArc]
  · intro i hi hj
    simpa [cycleArc] using clockwise_chain_getElem ha hp i hi

/-- A directed path is an interval of cycle edges, in one of the two
directions. This statement applies to every simple path, including those
crossing the label `n-1`/`0` boundary. -/
theorem cycle_path_is_arc {n : Nat} {p : Queue} (hp : p ≠ []) (hnd : p.Nodup)
    (hlabels : ∀ x ∈ p, x < n) (hpath : pathEdges (cycleAdjacent n) p = true) :
    ∃ a, a < n ∧ (p = cycleArc n a (p.length - 1) ∨
      p.reverse = cycleArc n a (p.length - 1)) := by
  rcases cycle_path_direction hnd hlabels hpath with hh | hh
  · cases p with
    | nil => exact False.elim (hp rfl)
    | cons a tail =>
      have ha := hlabels a (by simp)
      exact ⟨a, ha, Or.inl (by simpa using clockwise_chain_eq_arc ha hh)⟩
  · have hr : p.reverse.IsChain (Clockwise n) := by simpa only [List.isChain_reverse] using hh
    have hne : p.reverse ≠ [] := by simpa using hp
    cases he : p.reverse with
    | nil => exact False.elim (hne he)
    | cons a tail =>
      have ha := hlabels a (by simpa using (show a ∈ p.reverse by simp [he]))
      have har := clockwise_chain_eq_arc ha (by simpa [he] using hr)
      have hl : tail.length = p.length - 1 := by
        have hh := congrArg List.length he
        simp only [List.length_reverse, List.length_cons] at hh
        omega
      exact ⟨a, ha, Or.inr (by simpa [he, hl] using har)⟩

end OddCycle
