import OddCycle.CompletionFrontier

/-! A nonempty cycle scan frontier has at most one unused neighbor after
a positive replacement budget. Thus a completion can reverse at most one
cycle edge. -/

namespace OddCycle

theorem cycle_degree_two {n v a b c : Nat} (hn : 3 ≤ n)
    (hv : v < n) (ha : a < n) (hb : b < n) (hc : c < n)
    (hva : cycleAdjacent n v a = true) (hvb : cycleAdjacent n v b = true)
    (hvc : cycleAdjacent n v c = true) : a = b ∨ a = c ∨ b = c := by
  have ea := (cycleAdjacent_iff hv ha).mp hva
  have eb := (cycleAdjacent_iff hv hb).mp hvb
  have ec := (cycleAdjacent_iff hv hc).mp hvc
  rcases ea with ea | ea | ea | ea <;>
    rcases eb with eb | eb | eb | eb <;>
    rcases ec with ec | ec | ec | ec <;> omega

theorem scanFrontier_prior_neighbor {adj : Nat → Nat → Bool} {q : Queue}
    {budget job : Nat} (hw : 1 ≤ budget) (hnd : (job :: q).Nodup)
    (ht : (scanFrontier adj budget job q).untouched ≠ []) :
    ∃ u, u ∈ (scanFrontier adj budget job q).chain ∧
      u ∉ (scanFrontier adj budget job q).untouched ∧
      adj u (scanFrontier adj budget job q).carried = true := by
  let f := scanFrontier adj budget job q
  have hlast := scanFrontier_chain_last adj q budget job
  obtain ⟨p, hp⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen := scanFrontier_exhausted adj q budget job ht
  change f.chain = p ++ [f.carried] at hp
  cases p using List.reverseRecOn with
  | nil =>
    have he : f.chain.length = 1 := by simp [hp]
    change f.chain.length = budget + 1 at hlen
    omega
  | append_singleton p u =>
    have hu : u ∈ f.chain := by simp [hp]
    have hdis := List.disjoint_of_nodup_append
      (hnd.sublist (scanFrontier_chain_untouched_sublist adj q budget job))
    refine ⟨u, hu, List.disjoint_left.mp hdis hu, ?_⟩
    have hpath : f.chain.IsChain (fun a b => adj a b = true) :=
      (pathEdges_iff_isChain _ _).mp (scanFrontier_chain_path adj q budget job)
    rw [hp] at hpath
    have hpath' : (p ++ u :: f.carried :: []).IsChain (fun a b => adj a b = true) := by
      simpa only [List.append_assoc, List.singleton_append] using hpath
    exact (List.isChain_append_cons_cons.mp hpath').2.1

theorem scanFrontier_unique_cycle_neighbor {n w job : Nat} {q : Queue}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hnd : (job :: q).Nodup)
    (hlabels : ∀ x ∈ job :: q, x < n) {a b : Nat}
    (ha : a ∈ (scanFrontier (cycleAdjacent n) w job q).untouched)
    (hb : b ∈ (scanFrontier (cycleAdjacent n) w job q).untouched)
    (hea : cycleAdjacent n (scanFrontier (cycleAdjacent n) w job q).carried a = true)
    (heb : cycleAdjacent n (scanFrontier (cycleAdjacent n) w job q).carried b = true) : a = b := by
  let f := scanFrontier (cycleAdjacent n) w job q
  have ht : f.untouched ≠ [] := List.ne_nil_of_mem ha
  obtain ⟨u, hu, hunot, hue⟩ := scanFrontier_prior_neighbor hw hnd ht
  have hsub := scanFrontier_chain_untouched_sublist (cycleAdjacent n) q w job
  have hc : f.carried ∈ f.chain := List.mem_of_mem_getLast? (scanFrontier_chain_last _ q w job)
  have hv := hlabels f.carried (hsub.subset (List.mem_append_left _ hc))
  have hua := hlabels u (hsub.subset (List.mem_append_left _ hu))
  have hla := hlabels a (hsub.subset (List.mem_append_right _ ha))
  have hlb := hlabels b (hsub.subset (List.mem_append_right _ hb))
  have he := cycle_degree_two hn hv hla hlb hua hea heb
    (by simpa only [cycleAdjacent_symm n] using hue)
  rcases he with he | he | he
  · exact he
  · exact False.elim (hunot (he ▸ ha))
  · exact False.elim (hunot (he ▸ hb))

theorem EdgeEquiv.erase {adj : Nat → Nat → Bool} {q r : Queue}
    (h : EdgeEquiv adj q r) (a b : Nat) : EdgeEquiv (eraseEdge adj a b) q r := by
  intro x y hxy
  simp only [eraseEdge, Bool.and_eq_true] at hxy
  exact h x y hxy.1

theorem carry_cycle_edgeEquiv_erase {n w job y : Nat} {q : Queue}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hnd : (job :: q).Nodup)
    (hlabels : ∀ x ∈ job :: q, x < n)
    (hy : y ∈ (scanFrontier (cycleAdjacent n) w job q).untouched)
    (hey : cycleAdjacent n (scanFrontier (cycleAdjacent n) w job q).carried y = true) :
    EdgeEquiv (eraseEdge (cycleAdjacent n) (scanFrontier (cycleAdjacent n) w job q).carried y)
      (job :: q) ((carry (cycleAdjacent n) w job q).1 ++ [(carry (cycleAdjacent n) w job q).2]) := by
  let f := scanFrontier (cycleAdjacent n) w job q
  have hno : ∀ z ∈ f.untouched, eraseEdge (cycleAdjacent n) f.carried y f.carried z = false := by
    intro z hz
    by_cases hez : cycleAdjacent n f.carried z = true
    · have heq := scanFrontier_unique_cycle_neighbor hn hw hnd hlabels hz hy hez hey
      simp [eraseEdge, heq]
    · simp [eraseEdge, hez]
  have hh := ((scanFrontier_edgeEquiv (cycleAdjacent_symm n) q w job).erase f.carried y).trans
    ((edgeEquiv_move (eraseEdge_symm (cycleAdjacent_symm n) f.carried y) hno).append_left f.processed)
  simpa only [scanFrontier_result, List.append_assoc] using hh

/-- Every changed scan has a directed path of `w+1` edges ending in the
only edge that can change. The path is in the original queue word. -/
theorem carry_cycle_changed_path {n w job : Nat} {q : Queue}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hnd : (job :: q).Nodup)
    (hlabels : ∀ x ∈ job :: q, x < n)
    (hchange : ¬ EdgeEquiv (cycleAdjacent n) (job :: q)
      ((carry (cycleAdjacent n) w job q).1 ++ [(carry (cycleAdjacent n) w job q).2])) :
    ∃ p u v, (p ++ [u, v]).Sublist (job :: q) ∧
      pathEdges (cycleAdjacent n) (p ++ [u, v]) = true ∧
      p.length = w ∧ cycleAdjacent n u v = true ∧
      EdgeEquiv (eraseEdge (cycleAdjacent n) u v) (job :: q)
        ((carry (cycleAdjacent n) w job q).1 ++ [(carry (cycleAdjacent n) w job q).2]) := by
  obtain ⟨v, hv, hev⟩ := carry_orientation_change_requires_frontier_edge (cycleAdjacent_symm n) hchange
  let f := scanFrontier (cycleAdjacent n) w job q
  obtain ⟨p, hp⟩ := List.getLast?_eq_some_iff.mp (scanFrontier_chain_last (cycleAdjacent n) q w job)
  change f.chain = p ++ [f.carried] at hp
  have hsub := ((List.singleton_sublist.mpr hv).append_left f.chain).trans
    (scanFrontier_chain_untouched_sublist (cycleAdjacent n) q w job)
  have hpath : pathEdges (cycleAdjacent n) (f.chain ++ [v]) = true := by
    rw [pathEdges_iff_isChain, List.isChain_append]
    refine ⟨(pathEdges_iff_isChain _ _).mp (scanFrontier_chain_path _ q w job), by simp, ?_⟩
    intro a ha b hb
    have hea : a = f.carried := by simpa [hp] using ha.symm
    have heb : b = v := by simpa using hb.symm
    simpa only [hea, heb] using hev
  have hlen := scanFrontier_exhausted (cycleAdjacent n) q w job (List.ne_nil_of_mem hv)
  change f.chain.length = w + 1 at hlen
  rw [hp] at hlen
  refine ⟨p, f.carried, v, ?_, ?_, by simpa using hlen, hev,
    carry_cycle_edgeEquiv_erase hn hw hnd hlabels hv hev⟩
  · simpa [hp, List.append_assoc] using hsub
  · simpa [hp, List.append_assoc] using hpath

theorem complete_cycle_changed_path {n w pos initiating departed : Nat} {q rest : Queue}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hnd : q.Nodup) (hlabels : ∀ x ∈ q, x < n)
    (he : complete (cycleAdjacent n) w q pos = some (rest, departed, initiating))
    (hchange : ¬ EdgeEquiv (cycleAdjacent n) q (rest ++ [departed])) :
    ∃ p u v, (p ++ [u, v]).Sublist q ∧
      pathEdges (cycleAdjacent n) (p ++ [u, v]) = true ∧ p.length = w ∧
      cycleAdjacent n u v = true ∧ EdgeEquiv (eraseEdge (cycleAdjacent n) u v) q (rest ++ [departed]) := by
  induction q generalizing pos rest departed initiating with
  | nil => simp [complete] at he
  | cons a q ih =>
    cases pos with
    | zero =>
      simp only [complete, Option.some.injEq, Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl, rfl⟩
      exact carry_cycle_changed_path hn hw hnd hlabels hchange
    | succ pos =>
      cases hc : complete (cycleAdjacent n) w q pos with
      | none => simp [complete, hc] at he
      | some result =>
        obtain ⟨r, d, i⟩ := result
        simp [complete, hc] at he
        rcases he with ⟨rfl, rfl, rfl⟩
        have hch : ¬ EdgeEquiv (cycleAdjacent n) q (r ++ [d]) :=
          fun hh => hchange (hh.cons a)
        obtain ⟨p, u, v, hp, hpath, hlen, hadj, heq⟩ :=
          ih (List.nodup_cons.mp hnd).2 (fun x hx => hlabels x (by simp [hx])) hc hch
        exact ⟨p, u, v, hp.cons a, hpath, hlen, hadj, heq.cons a⟩

theorem first_transition_changed_path {n w pos initiating : Nat} {s t : State}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hs : Valid n s)
    (he : transition (cycleAdjacent n) w s false pos = some (t, initiating))
    (hchange : orientation n s ≠ orientation n t) :
    ∃ p u v, (p ++ [u, v]).Sublist (placement s) ∧
      pathEdges (cycleAdjacent n) (p ++ [u, v]) = true ∧ p.length = w ∧
      cycleAdjacent n u v = true ∧
      EdgeEquiv (eraseEdge (cycleAdjacent n) u v) (placement s) (placement t) := by
  cases hc : complete (cycleAdjacent n) w s.1 pos with
  | none => simp [transition, hc] at he
  | some result =>
    obtain ⟨r, d, i⟩ := result
    simp [transition, hc] at he
    rcases he with ⟨rfl, rfl⟩
    have hq : s.1.Sublist (placement s) := List.sublist_append_left _ _
    have hnd := hs.placement_nodup.sublist hq
    have hlabels : ∀ x ∈ s.1, x < n := fun x hx => hs.placement_mem.mp (hq.subset hx)
    have hch : ¬ EdgeEquiv (cycleAdjacent n) s.1 (r ++ [d]) := by
      intro hh
      apply hchange
      apply EdgeEquiv.orientation_eq
      simpa [placement, List.append_assoc] using hh.append_right s.2.reverse
    obtain ⟨p, u, v, hp, hpath, hlen, hadj, heq⟩ :=
      complete_cycle_changed_path hn hw hnd hlabels hc hch
    refine ⟨p, u, v, hp.trans hq, hpath, hlen, hadj, ?_⟩
    simpa [placement, List.append_assoc] using heq.append_right s.2.reverse

/-- The necessity statement for either completing queue. Queue exchange
reverses placement, giving the opposite-side path condition in the second
queue. The edge-order conclusion is on the original placements. -/
theorem transition_changed_path {n w pos initiating : Nat} {s t : State} {side : Bool}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hs : Valid n s)
    (he : transition (cycleAdjacent n) w s side pos = some (t, initiating))
    (hchange : orientation n s ≠ orientation n t) :
    ∃ p u v, (p ++ [u, v]).Sublist (placement (if side then exchange s else s)) ∧
      pathEdges (cycleAdjacent n) (p ++ [u, v]) = true ∧ p.length = w ∧
      cycleAdjacent n u v = true ∧
      EdgeEquiv (eraseEdge (cycleAdjacent n) u v) (placement s) (placement t) := by
  cases side with
  | false => exact first_transition_changed_path hn hw hs he hchange
  | true =>
    have ht := transition_valid hs he
    have hchange' : orientation n (exchange s) ≠ orientation n (exchange t) := by
      intro hh
      apply hchange
      simpa only [exchange_exchange] using orientation_exchange_eq
        (by omega : 0 < n) hs.exchange ht.exchange hh
    obtain ⟨p, u, v, hp, hpath, hlen, hadj, heq⟩ :=
      first_transition_changed_path hn hw hs.exchange (transition_exchange he) hchange'
    refine ⟨p, u, v, hp, hpath, hlen, hadj, ?_⟩
    simpa only [placement_exchange, List.reverse_reverse] using heq.reverse

end OddCycle
