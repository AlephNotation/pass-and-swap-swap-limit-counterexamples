import OddCycle.ShortOrientation

/-!
The frontier of a limited replacement scan. The processed prefix has already
undergone unlimited pass-and-swap; only moving the current carried job past
the untouched suffix can change edge orders. This is an operational invariant
for arbitrary symmetric swapping graphs.
-/

namespace OddCycle

structure ScanFrontier where
  processed : Queue
  carried : Nat
  untouched : Queue
  chain : Queue
  deriving DecidableEq

def scanFrontier (adj : Nat → Nat → Bool) (budget job : Nat) : Queue → ScanFrontier
  | [] => ⟨[], job, [], [job]⟩
  | x :: xs =>
    if budget = 0 then ⟨[], job, x :: xs, [job]⟩
    else if adj job x then
      let f := scanFrontier adj (budget - 1) x xs
      ⟨job :: f.processed, f.carried, f.untouched, job :: f.chain⟩
    else
      let f := scanFrontier adj budget job xs
      ⟨x :: f.processed, f.carried, f.untouched, f.chain⟩

theorem scanFrontier_result (adj : Nat → Nat → Bool) (q : Queue) (budget job : Nat) :
    carry adj budget job q =
      ((scanFrontier adj budget job q).processed ++ (scanFrontier adj budget job q).untouched,
        (scanFrontier adj budget job q).carried) := by
  induction q generalizing budget job with
  | nil => rfl
  | cons x xs ih =>
    by_cases hz : budget = 0
    · simp [carry, scanFrontier, hz]
    · by_cases ha : adj job x = true
      · simp [carry, scanFrontier, hz, ha, ih]
      · simp [carry, scanFrontier, hz, ha, ih]

theorem scanFrontier_edgeEquiv {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) (q : Queue) (budget job : Nat) :
    EdgeEquiv adj (job :: q)
      ((scanFrontier adj budget job q).processed ++
        (scanFrontier adj budget job q).carried :: (scanFrontier adj budget job q).untouched) := by
  induction q generalizing budget job with
  | nil => exact .refl _ _
  | cons x xs ih =>
    by_cases hz : budget = 0
    · simpa [scanFrontier, hz] using EdgeEquiv.refl adj (job :: x :: xs)
    · by_cases ha : adj job x = true
      · simpa [scanFrontier, hz, ha] using (ih (budget - 1) x).cons job
      · have hh := (edgeEquiv_swap hsym (Bool.eq_false_iff.mpr ha) xs).trans ((ih budget job).cons x)
        simpa [scanFrontier, hz, ha] using hh

theorem scanFrontier_chain_head (adj : Nat → Nat → Bool) (q : Queue) (budget job : Nat) :
    (scanFrontier adj budget job q).chain.head? = some job := by
  induction q generalizing budget job with
  | nil => rfl
  | cons x xs ih =>
    by_cases hz : budget = 0
    · simp [scanFrontier, hz]
    · by_cases ha : adj job x = true
      · simp [scanFrontier, hz, ha]
      · simpa [scanFrontier, hz, ha] using ih budget job

theorem scanFrontier_chain_sublist (adj : Nat → Nat → Bool) (q : Queue) (budget job : Nat) :
    (scanFrontier adj budget job q).chain.Sublist (job :: q) := by
  induction q generalizing budget job with
  | nil => exact .refl _
  | cons x xs ih =>
    by_cases hz : budget = 0
    · simp [scanFrontier, hz]
    · by_cases ha : adj job x = true
      · simpa [scanFrontier, hz, ha] using (ih (budget - 1) x).cons_cons job
      · have hh := (ih budget job).trans
          (show (job :: xs).Sublist (job :: x :: xs) from (List.sublist_cons_self x xs).cons_cons job)
        simpa [scanFrontier, hz, ha] using hh

theorem scanFrontier_chain_path (adj : Nat → Nat → Bool) (q : Queue) (budget job : Nat) :
    pathEdges adj (scanFrontier adj budget job q).chain = true := by
  induction q generalizing budget job with
  | nil => rfl
  | cons x xs ih =>
    by_cases hz : budget = 0
    · simp [scanFrontier, hz, pathEdges]
    · by_cases ha : adj job x = true
      · have hhead := scanFrontier_chain_head adj xs (budget - 1) x
        have hp := ih (budget - 1) x
        cases hc : (scanFrontier adj (budget - 1) x xs).chain with
        | nil => simp [hc] at hhead
        | cons a tail =>
          have hax : a = x := by simpa only [hc, List.head?_cons, Option.some.injEq] using hhead
          subst a
          simpa [scanFrontier, hz, ha, hc, pathEdges] using hp
      · simpa [scanFrontier, hz, ha] using ih budget job

theorem scanFrontier_chain_length (adj : Nat → Nat → Bool) (q : Queue) (budget job : Nat) :
    (scanFrontier adj budget job q).chain.length ≤ budget + 1 := by
  induction q generalizing budget job with
  | nil => simp [scanFrontier]
  | cons x xs ih =>
    by_cases hz : budget = 0
    · simp [scanFrontier, hz]
    · by_cases ha : adj job x = true
      · have hh := ih (budget - 1) x
        simp only [scanFrontier, hz, if_false, ha, if_true, List.length_cons]
        omega
      · simpa [scanFrontier, hz, ha] using ih budget job

/-- A nonempty untouched suffix certifies that the budget was exhausted. -/
theorem scanFrontier_exhausted (adj : Nat → Nat → Bool) (q : Queue) (budget job : Nat)
    (htail : (scanFrontier adj budget job q).untouched ≠ []) :
    (scanFrontier adj budget job q).chain.length = budget + 1 := by
  induction q generalizing budget job with
  | nil => simp [scanFrontier] at htail
  | cons x xs ih =>
    by_cases hz : budget = 0
    · simp [scanFrontier, hz]
    · by_cases ha : adj job x = true
      · have ht : (scanFrontier adj (budget - 1) x xs).untouched ≠ [] := by
          simpa [scanFrontier, hz, ha] using htail
        have hh := ih (budget - 1) x ht
        simp only [scanFrontier, hz, if_false, ha, if_true, List.length_cons, hh]
        omega
      · have ht : (scanFrontier adj budget job xs).untouched ≠ [] := by
          simpa [scanFrontier, hz, ha] using htail
        simpa [scanFrontier, hz, ha] using ih budget job ht

theorem scanFrontier_chain_last (adj : Nat → Nat → Bool) (q : Queue) (budget job : Nat) :
    (scanFrontier adj budget job q).chain.getLast? =
      some (scanFrontier adj budget job q).carried := by
  induction q generalizing budget job with
  | nil => rfl
  | cons x xs ih =>
    by_cases hz : budget = 0
    · simp [scanFrontier, hz]
    · by_cases ha : adj job x = true
      · have hh := ih (budget - 1) x
        have hhead := scanFrontier_chain_head adj xs (budget - 1) x
        cases hc : (scanFrontier adj (budget - 1) x xs).chain with
        | nil => simp [hc] at hhead
        | cons a tail => simpa [scanFrontier, hz, ha, hc] using hh
      · simpa [scanFrontier, hz, ha] using ih budget job

theorem scanFrontier_population (adj : Nat → Nat → Bool) (q : Queue) (budget job : Nat) :
    ((scanFrontier adj budget job q).processed ++
      (scanFrontier adj budget job q).carried :: (scanFrontier adj budget job q).untouched).Perm
      (job :: q) := by
  induction q generalizing budget job with
  | nil => exact .refl _
  | cons x xs ih =>
    by_cases hz : budget = 0
    · simp [scanFrontier, hz]
    · by_cases ha : adj job x = true
      · simpa [scanFrontier, hz, ha] using (ih (budget - 1) x).cons job
      · have hh := ((ih budget job).cons x).trans (List.Perm.swap job x xs)
        simpa [scanFrontier, hz, ha] using hh

theorem scanFrontier_chain_untouched_sublist (adj : Nat → Nat → Bool)
    (q : Queue) (budget job : Nat) :
    ((scanFrontier adj budget job q).chain ++ (scanFrontier adj budget job q).untouched).Sublist
      (job :: q) := by
  induction q generalizing budget job with
  | nil => exact .refl _
  | cons x xs ih =>
    by_cases hz : budget = 0
    · simp [scanFrontier, hz]
    · by_cases ha : adj job x = true
      · simpa [scanFrontier, hz, ha] using (ih (budget - 1) x).cons_cons job
      · have hh := (ih budget job).trans
          (show (job :: xs).Sublist (job :: x :: xs) from (List.sublist_cons_self x xs).cons_cons job)
        simpa [scanFrontier, hz, ha] using hh

theorem scanFrontier_long_path {adj : Nat → Nat → Bool} {q : Queue} {budget job y : Nat}
    (hy : y ∈ (scanFrontier adj budget job q).untouched)
    (ha : adj (scanFrontier adj budget job q).carried y = true) :
    ∃ p, p.Sublist (job :: q) ∧ pathEdges adj p = true ∧ p.length = budget + 2 := by
  let f := scanFrontier adj budget job q
  refine ⟨f.chain ++ [y], ?_, ?_, ?_⟩
  · exact ((List.singleton_sublist.mpr hy).append_left f.chain).trans
      (scanFrontier_chain_untouched_sublist adj q budget job)
  · rw [pathEdges_iff_isChain, List.isChain_append]
    refine ⟨(pathEdges_iff_isChain _ _).mp (scanFrontier_chain_path adj q budget job), by simp, ?_⟩
    intro a ha' b hb'
    have he : a = f.carried := by
      have hh : f.chain.getLast? = some f.carried := scanFrontier_chain_last adj q budget job
      have hm : f.chain.getLast? = some a := ha'
      exact Option.some.inj (hm.symm.trans hh)
    have hb : b = y := by simpa using hb'.symm
    simpa only [he, hb] using ha
  · have ht : f.untouched ≠ [] := List.ne_nil_of_mem hy
    have he := scanFrontier_exhausted adj q budget job ht
    simpa only [List.length_append, List.length_singleton, he, Nat.add_assoc] using
      (show f.chain.length + 1 = budget + 1 + 1 by rw [he])

theorem carry_orientation_change_requires_frontier_edge {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) {q : Queue} {budget job : Nat}
    (hchange : ¬ EdgeEquiv adj (job :: q)
      ((carry adj budget job q).1 ++ [(carry adj budget job q).2])) :
    ∃ y ∈ (scanFrontier adj budget job q).untouched,
      adj (scanFrontier adj budget job q).carried y = true := by
  by_contra hn
  have hno : ∀ y ∈ (scanFrontier adj budget job q).untouched,
      adj (scanFrontier adj budget job q).carried y = false := by
    intro y hy
    by_cases ha : adj (scanFrontier adj budget job q).carried y = true
    · exact False.elim (hn ⟨y, hy, ha⟩)
    · exact Bool.eq_false_iff.mpr ha
  apply hchange
  have hh := (scanFrontier_edgeEquiv hsym q budget job).trans
    ((edgeEquiv_move hsym hno).append_left (scanFrontier adj budget job q).processed)
  simpa only [scanFrontier_result, List.append_assoc] using hh

end OddCycle
