import OddCycle.CycleFrontier

/-! Realizing a prescribed cycle path by the greedy operational scan. -/

namespace OddCycle

theorem before_of_pair_sublist {a b : Nat} {q : Queue}
    (hnd : q.Nodup) (hsub : [a, b].Sublist q) : q.idxOf a < q.idxOf b := by
  have hp : q.Pairwise (fun x y => q.idxOf x < q.idxOf y) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [hnd.idxOf_getElem i hi, hnd.idxOf_getElem j hj] using hij
  simpa using hp.sublist hsub

/-- The current carried job crosses every untouched job when it departs. -/
theorem scanFrontier_crosses_untouched {adj : Nat → Nat → Bool}
    {q : Queue} {budget job y : Nat} (hnd : (job :: q).Nodup)
    (hy : y ∈ (scanFrontier adj budget job q).untouched) :
    (job :: q).idxOf (scanFrontier adj budget job q).carried < (job :: q).idxOf y ∧
    ((carry adj budget job q).1 ++ [(carry adj budget job q).2]).idxOf y <
      ((carry adj budget job q).1 ++ [(carry adj budget job q).2]).idxOf
        (scanFrontier adj budget job q).carried := by
  let f := scanFrontier adj budget job q
  have hc : f.carried ∈ f.chain :=
    List.mem_of_mem_getLast? (scanFrontier_chain_last adj q budget job)
  have hsub : [f.carried, y].Sublist (job :: q) :=
    ((List.singleton_sublist.mpr hc).append (List.singleton_sublist.mpr hy)).trans
      (scanFrontier_chain_untouched_sublist adj q budget job)
  refine ⟨before_of_pair_sublist hnd hsub, ?_⟩
  have hp : (f.processed ++ f.untouched ++ [f.carried]).Perm (job :: q) :=
    (show (f.processed ++ f.untouched ++ [f.carried]).Perm
      (f.processed ++ f.carried :: f.untouched) by
        simpa only [List.append_assoc, List.append_nil] using
          (List.perm_middle (l₁ := f.untouched) (l₂ := []) (a := f.carried)).append_left f.processed).trans
      (scanFrontier_population adj q budget job)
  have hs : [y, f.carried].Sublist (f.processed ++ f.untouched ++ [f.carried]) := by
    simpa only [List.append_assoc] using
      ((List.singleton_sublist.mpr hy).append_right [f.carried]).trans
        (List.sublist_append_right f.processed (f.untouched ++ [f.carried]))
  simpa only [scanFrontier_result] using before_of_pair_sublist (hp.nodup_iff.mpr hnd) hs

theorem carry_changes_of_frontier_neighbor {adj : Nat → Nat → Bool}
    {q : Queue} {budget job y : Nat} (hnd : (job :: q).Nodup)
    (hy : y ∈ (scanFrontier adj budget job q).untouched)
    (hadj : adj (scanFrontier adj budget job q).carried y = true) :
    ¬ EdgeEquiv adj (job :: q)
      ((carry adj budget job q).1 ++ [(carry adj budget job q).2]) := by
  intro he
  have hc := scanFrontier_crosses_untouched hnd hy
  have hh := (he.before_iff hadj).mp hc.1
  omega

/-- Once the first edge of a simple cycle path has been selected, degree two
forces the remaining replacements along that path. Intervening jobs are
incompatible with the carried job and are skipped. -/
theorem scanFrontier_follows_cycle {n : Nat} (hn : 3 ≤ n) (q : Queue)
    (previous job budget : Nat) (path : Queue)
    (hnd : (previous :: job :: q).Nodup)
    (hlabels : ∀ x ∈ previous :: job :: q, x < n)
    (hprev : cycleAdjacent n previous job = true)
    (hpath : pathEdges (cycleAdjacent n) (job :: path) = true)
    (hsub : path.Sublist q) (hlen : budget < path.length) :
    (scanFrontier (cycleAdjacent n) budget job q).chain = job :: path.take budget ∧
    (path.drop budget).Sublist (scanFrontier (cycleAdjacent n) budget job q).untouched := by
  induction q generalizing previous job budget path with
  | nil =>
    have : path = [] := List.sublist_nil.mp hsub
    simp [this] at hlen
  | cons x xs ih =>
    cases budget with
    | zero => simpa [scanFrontier] using hsub
    | succ budget =>
      cases path with
      | nil => simp at hlen
      | cons target more =>
        have hp : cycleAdjacent n job target = true ∧
            pathEdges (cycleAdjacent n) (target :: more) = true := by
          simpa only [pathEdges, Bool.and_eq_true] using hpath
        have hadj := hp.1
        have hrest := hp.2
        by_cases he : x = target
        · subst x
          have hh := ih job target budget more (List.nodup_cons.mp hnd).2
            (fun a ha => hlabels a (List.mem_cons_of_mem _ ha)) hadj hrest
            (List.cons_sublist_cons.mp hsub) (by simpa using hlen)
          simpa [scanFrontier, hadj] using hh
        · have hsub' : (target :: more).Sublist xs := by
            rcases List.sublist_cons_iff.mp hsub with hh | ⟨r, hr, _⟩
            · exact hh
            · exact False.elim (he (List.cons.inj hr).1.symm)
          have hno : cycleAdjacent n job x = false := by
            apply Bool.eq_false_iff.mpr
            intro hx
            have hm : target ∈ x :: xs := hsub.subset (by simp)
            have hp := (List.nodup_cons.mp hnd).1
            have htprev : previous ≠ target := fun e => hp (by simp [e, hm])
            have hxprev : previous ≠ x := fun e => hp (by simp [e])
            have hd := cycle_degree_two hn
              (hlabels job (by simp)) (hlabels previous (by simp))
              (hlabels target (by simp [hm])) (hlabels x (by simp))
              (by simpa only [cycleAdjacent_symm n] using hprev) hadj hx
            exact hd.elim htprev (fun h => h.elim hxprev (fun h => he h.symm))
          have hs : (previous :: job :: xs).Sublist (previous :: job :: x :: xs) :=
            (List.sublist_cons_self x xs).cons_cons job |>.cons_cons previous
          have hnd' : (previous :: job :: xs).Nodup := hnd.sublist hs
          have hh := ih previous job (budget + 1) (target :: more) hnd'
            (fun a ha => hlabels a (hs.subset ha))
            hprev hpath hsub' hlen
          simpa [scanFrontier, hno] using hh

theorem scanFrontier_follows_cycle_first {n w job next : Nat} {q path : Queue}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hnd : (job :: next :: q).Nodup)
    (hlabels : ∀ x ∈ job :: next :: q, x < n)
    (hpath : pathEdges (cycleAdjacent n) (job :: next :: path) = true)
    (hsub : path.Sublist q) (hlen : w ≤ path.length) :
    (scanFrontier (cycleAdjacent n) w job (next :: q)).chain =
      (job :: next :: path).take (w + 1) ∧
    ((job :: next :: path).drop (w + 1)).Sublist
      (scanFrontier (cycleAdjacent n) w job (next :: q)).untouched := by
  have hp : cycleAdjacent n job next = true ∧
      pathEdges (cycleAdjacent n) (next :: path) = true := by
    simpa only [pathEdges, Bool.and_eq_true] using hpath
  have hh := scanFrontier_follows_cycle hn q job next (w - 1) path
    hnd hlabels hp.1 hp.2 hsub (by omega)
  obtain ⟨b, rfl⟩ : ∃ b, w = b + 1 := ⟨w - 1, by omega⟩
  simpa [scanFrontier, hp.1, List.take_succ_cons, List.drop_succ_cons] using hh

theorem cons_sublist_split {a : Nat} {path q : Queue} (h : (a :: path).Sublist q) :
    ∃ pre tail, q = pre ++ a :: tail ∧ path.Sublist tail := by
  induction q with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.sublist_cons_iff.mp h with hh | ⟨r, hr, hs⟩
    · obtain ⟨pre, tail, he, ht⟩ := ih hh
      exact ⟨x :: pre, tail, by simp [he], ht⟩
    · have ha := (List.cons.inj hr).1
      have hp := (List.cons.inj hr).2
      subst x
      subst r
      exact ⟨[], xs, rfl, hs⟩

/-- Moving the second vertex of a directed cycle path next to its first
vertex crosses no incident edge, so the prescribed first replacement can
always be selected without changing the orientation. -/
theorem cycle_path_force_first {n job next after : Nat} {pre middle tail : Queue}
    (hn : 3 ≤ n) (hnd : (pre ++ job :: (middle ++ next :: tail)).Nodup)
    (hlabels : ∀ x ∈ pre ++ job :: (middle ++ next :: tail), x < n)
    (hfirst : cycleAdjacent n job next = true)
    (hsecond : cycleAdjacent n next after = true) (ha : after ∈ tail) :
    WordReachable (cycleAdjacent n)
      (pre ++ job :: (middle ++ next :: tail))
      (pre ++ job :: next :: (middle ++ tail)) := by
  have hn' : (job :: (middle ++ next :: tail)).Nodup :=
    hnd.sublist (List.sublist_append_right _ _)
  have hjob := (List.nodup_cons.mp hn').1
  have hm := List.disjoint_of_nodup_append (List.nodup_cons.mp hn').2
  have hjnext : job ≠ after := fun he => hjob (by simp [he, ha])
  have hfree : ∀ x ∈ middle, cycleAdjacent n next x = false := by
    intro x hx
    apply Bool.eq_false_iff.mpr
    intro hadj
    have hjx : job ≠ x := fun he => hjob (by simp [he, hx])
    have hax : after ≠ x := fun he =>
      (List.disjoint_left.mp hm hx) (by simp [← he, ha])
    have hd := cycle_degree_two hn
      (hlabels next (by simp)) (hlabels job (by simp))
      (hlabels after (by simp [ha])) (hlabels x (by simp [hx]))
      (by simpa only [cycleAdjacent_symm n] using hfirst) hsecond hadj
    exact hd.elim hjnext (fun h => h.elim hjx hax)
  simpa only [List.append_assoc, List.singleton_append] using
    (word_move_left (cycleAdjacent_symm n) middle tail next hfree).prepend (pre ++ [job])

theorem WordReachable.perm {adj : Nat → Nat → Bool} {q r : Queue}
    (h : WordReachable adj q r) : q.Perm r := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih =>
    cases hs with
    | swap pre post x y _ => exact ih.trans ((List.Perm.swap y x post).append_left pre)

theorem cycle_path_representative {n job next after : Nat} {path q : Queue}
    (hn : 3 ≤ n) (hnd : q.Nodup) (hlabels : ∀ x ∈ q, x < n)
    (hsub : (job :: next :: after :: path).Sublist q)
    (hpath : pathEdges (cycleAdjacent n) (job :: next :: after :: path) = true) :
    ∃ pre suffix, WordReachable (cycleAdjacent n) q (pre ++ job :: next :: suffix) ∧
      (after :: path).Sublist suffix := by
  obtain ⟨pre, rest, rfl, hs⟩ := cons_sublist_split hsub
  obtain ⟨middle, tail, rfl, ht⟩ := cons_sublist_split hs
  have hp : cycleAdjacent n job next = true ∧
      cycleAdjacent n next after = true ∧
      pathEdges (cycleAdjacent n) (after :: path) = true := by
    simpa only [pathEdges, Bool.and_eq_true] using hpath
  exact ⟨pre, middle ++ tail,
    cycle_path_force_first hn hnd hlabels hp.1 hp.2.1 (ht.subset (by simp)),
    ht.trans (List.sublist_append_right _ _)⟩

/-- Every directed cycle path of length `w+1` can be made the greedy
replacement path up to the budget, with its final vertex still untouched. -/
theorem cycle_path_realize_frontier {n w job next : Nat} {path q : Queue}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hnd : q.Nodup) (hlabels : ∀ x ∈ q, x < n)
    (hsub : (job :: next :: path).Sublist q)
    (hpath : pathEdges (cycleAdjacent n) (job :: next :: path) = true)
    (hlen : path.length = w) :
    ∃ pre suffix, WordReachable (cycleAdjacent n) q (pre ++ job :: next :: suffix) ∧
      (scanFrontier (cycleAdjacent n) w job (next :: suffix)).chain =
        (job :: next :: path).take (w + 1) ∧
      ((job :: next :: path).drop (w + 1)).Sublist
        (scanFrontier (cycleAdjacent n) w job (next :: suffix)).untouched := by
  cases path with
  | nil => simp at hlen; omega
  | cons after path =>
    obtain ⟨pre, suffix, hr, hs⟩ := cycle_path_representative hn hnd hlabels hsub hpath
    have hp := hr.perm
    have hnd' := (hp.nodup_iff.mp hnd).sublist (List.sublist_append_right pre _)
    have hl : ∀ x ∈ job :: next :: suffix, x < n :=
      fun x hx => hlabels x (hp.mem_iff.mpr (List.mem_append_right _ hx))
    exact ⟨pre, suffix, hr, scanFrontier_follows_cycle_first hn hw hnd' hl hpath hs hlen.ge⟩

theorem cycle_path_realize_last_edge {n w u v : Nat} {p q : Queue}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hnd : q.Nodup) (hlabels : ∀ x ∈ q, x < n)
    (hsub : (p ++ [u, v]).Sublist q)
    (hpath : pathEdges (cycleAdjacent n) (p ++ [u, v]) = true) (hlen : p.length = w) :
    ∃ pre job suffix, WordReachable (cycleAdjacent n) q (pre ++ job :: suffix) ∧
      (scanFrontier (cycleAdjacent n) w job suffix).carried = u ∧
      v ∈ (scanFrontier (cycleAdjacent n) w job suffix).untouched := by
  have hreal : ∃ pre job suffix,
      WordReachable (cycleAdjacent n) q (pre ++ job :: suffix) ∧
      (scanFrontier (cycleAdjacent n) w job suffix).chain = (p ++ [u, v]).take (w + 1) ∧
      ((p ++ [u, v]).drop (w + 1)).Sublist
        (scanFrontier (cycleAdjacent n) w job suffix).untouched := by
    cases p with
    | nil => simp at hlen; omega
    | cons job p =>
      cases p with
      | nil =>
        obtain ⟨pre, suffix, hr, hc, ht⟩ := cycle_path_realize_frontier hn hw hnd hlabels
          hsub hpath (by simpa using hlen)
        exact ⟨pre, job, u :: suffix, hr, hc, ht⟩
      | cons next p =>
        obtain ⟨pre, suffix, hr, hc, ht⟩ := cycle_path_realize_frontier hn hw hnd hlabels
          hsub hpath (by simpa using hlen)
        exact ⟨pre, job, next :: suffix, hr, hc, ht⟩
  obtain ⟨pre, job, suffix, hr, hc, ht⟩ := hreal
  have he : p ++ [u, v] = (p ++ [u]) ++ [v] := by simp
  have hl : (p ++ [u]).length = w + 1 := by simp [hlen]
  rw [he, List.take_left' hl] at hc
  rw [he, List.drop_left' hl] at ht
  refine ⟨pre, job, suffix, hr, ?_, List.singleton_sublist.mp ht⟩
  have hh := scanFrontier_chain_last (cycleAdjacent n) suffix w job
  rw [hc] at hh
  simpa using hh.symm

/-- Operational sufficiency: after zero-replacement exchanges within the
orientation fiber, a completion reverses any specified last edge of a
directed `w+1`-edge cycle path, preserving every other cycle edge. -/
theorem cycle_path_realize_flip {n w u v : Nat} {p q : Queue}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hnd : q.Nodup) (hlabels : ∀ x ∈ q, x < n)
    (hsub : (p ++ [u, v]).Sublist q)
    (hpath : pathEdges (cycleAdjacent n) (p ++ [u, v]) = true) (hlen : p.length = w) :
    ∃ r rest departed initiating pos,
      WordReachable (cycleAdjacent n) q r ∧
      complete (cycleAdjacent n) w r pos = some (rest, departed, initiating) ∧
      EdgeEquiv (eraseEdge (cycleAdjacent n) u v) q (rest ++ [departed]) ∧
      (rest ++ [departed]).idxOf v < (rest ++ [departed]).idxOf u := by
  obtain ⟨pre, job, suffix, hr, hu, hv⟩ :=
    cycle_path_realize_last_edge hn hw hnd hlabels hsub hpath hlen
  have hp := hr.perm
  have hsubq : (job :: suffix).Sublist (pre ++ job :: suffix) := List.sublist_append_right _ _
  have hnd' := (hp.nodup_iff.mp hnd).sublist hsubq
  have hl : ∀ x ∈ job :: suffix, x < n := fun x hx => hlabels x (hp.mem_iff.mpr (hsubq.subset hx))
  have hadj : cycleAdjacent n u v = true := by
    have hchain := (pathEdges_iff_isChain _ _).mp hpath
    exact (List.isChain_append_cons_cons.mp hchain).2.1
  have he := carry_cycle_edgeEquiv_erase hn hw hnd' hl hv (by simpa [hu] using hadj)
  rw [hu] at he
  let c := carry (cycleAdjacent n) w job suffix
  refine ⟨pre ++ job :: suffix, pre ++ c.1, c.2, job, pre.length, hr, ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using complete_append pre
      (show complete (cycleAdjacent n) w (job :: suffix) 0 = some (c.1, c.2, job) from rfl)
  · simpa only [List.append_assoc] using
      ((hr.edgeEquiv (cycleAdjacent_symm n)).erase u v).trans (he.append_left pre)
  · have hc := (scanFrontier_crosses_untouched hnd' hv).2
    rw [hu] at hc
    have hpop : (c.1 ++ [c.2]).Perm (job :: suffix) := carry_population _ _ _ _
    have hm : u ∈ c.1 ++ [c.2] := by
      have : c.2 = u := by simpa only [c, scanFrontier_result] using hu
      simp [this]
    have hmv : v ∈ c.1 ++ [c.2] := hpop.mem_iff.mpr
      ((scanFrontier_chain_untouched_sublist (cycleAdjacent n) suffix w job).subset
        (List.mem_append_right _ hv))
    have hdis := List.disjoint_of_nodup_append (hp.nodup_iff.mp hnd)
    have hup : u ∉ pre := fun hx => List.disjoint_left.mp hdis hx (hpop.mem_iff.mp hm)
    have hvp : v ∉ pre := fun hx => List.disjoint_left.mp hdis hx (hpop.mem_iff.mp hmv)
    simpa only [List.append_assoc, List.idxOf_append, if_neg hup, if_neg hvp,
      Nat.add_lt_add_iff_right, c] using hc

end OddCycle
