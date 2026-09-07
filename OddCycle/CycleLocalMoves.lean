import OddCycle.EdgeBitFlips

/-! Identification of the operational directed-path moves with circular
homogeneous-block flips. -/

namespace OddCycle

theorem cycleArc_last_two (n a w : Nat) :
    cycleArc n a (w + 1) = (List.range w).map (fun i => (a + i) % n) ++
      [(a + w) % n, (a + w + 1) % n] := by
  simp only [cycleArc, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  congr 3

theorem cycleArc_first_two {n a : Nat} (ha : a < n) (w : Nat) :
    ∃ r, r.length = w ∧ cycleArc n a (w + 1) = a :: ((a + 1) % n) :: r := by
  refine ⟨(List.range w).map (fun i => (a + (i + 2)) % n), by simp, ?_⟩
  simp [cycleArc, List.range_succ_eq_map, List.map_map, Function.comp_def,
    Nat.mod_eq_of_lt ha, Nat.add_assoc]

theorem last_arc_directedPathFlip {n w a : Nat} {s t : State}
    (hn : 3 ≤ n) (hs : Valid n s) (ht : Valid n t)
    (hsub : (cycleArc n a (w + 1)).Sublist (placement s))
    (hflip : EdgeBitFlip n s t ((a + w) % n)) : DirectedPathFlip n w s t := by
  let u := (a + w) % n
  let v := (a + w + 1) % n
  change EdgeBitFlip n s t u at hflip
  have hu : u < n := Nat.mod_lt _ (by omega)
  have huv : (u + 1) % n = v := by simp only [u, v, Nat.mod_add_mod]
  have hb : edgeBit n s u = true :=
    (cycleArc_forward_sublist_iff (by omega) hs).mp hsub w (by omega)
  have hbt : edgeBit n t u = false := by simpa only [hb, Bool.not_true] using hflip.2
  have hrev : (placement t).idxOf v < (placement t).idxOf u := by
    simpa only [huv] using (edgeBit_false_iff (by omega) hu ht).mp hbt
  refine ⟨(List.range w).map (fun i => (a + i) % n), u, v, ?_, ?_, by simp, ?_, hrev⟩
  · simpa only [cycleArc_last_two, u, v] using hsub
  · simpa only [cycleArc_last_two, u, v] using cycleArc_path n a (w + 1)
  · simpa only [huv] using edgeEquiv_erase_of_bits hn hs ht hflip.1

theorem first_arc_directedPathFlip {n w a : Nat} {s t : State}
    (hn : 3 ≤ n) (ha : a < n) (hs : Valid n s) (ht : Valid n t)
    (hsub : (cycleArc n a (w + 1)).reverse.Sublist (placement s))
    (hflip : EdgeBitFlip n s t a) : DirectedPathFlip n w s t := by
  obtain ⟨r, hrlen, harc⟩ := cycleArc_first_two ha w
  have hb : edgeBit n s a = false := by
    have hh := (cycleArc_backward_sublist_iff (by omega) hs).mp hsub 0 (by omega)
    simpa only [Nat.add_zero, Nat.mod_eq_of_lt ha] using hh
  have hbt : edgeBit n t a = true := by simpa only [hb, Bool.not_false] using hflip.2
  have hrev : (placement t).idxOf a < (placement t).idxOf ((a + 1) % n) := by
    simpa only [edgeBit, decide_eq_true_eq] using hbt
  refine ⟨r.reverse, (a + 1) % n, a, ?_, ?_, by simpa using hrlen, ?_, hrev⟩
  · simpa only [harc, List.reverse_cons, List.append_assoc, List.singleton_append] using hsub
  · have hp := (pathEdges_reverse (cycleAdjacent_symm n) _).mpr (cycleArc_path n a (w + 1))
    simpa only [harc, List.reverse_cons, List.append_assoc, List.singleton_append] using hp
  · simpa only [EdgeEquiv, eraseEdge, Bool.or_comm] using edgeEquiv_erase_of_bits hn hs ht hflip.1

theorem edgeBit_exchange_not {n i : Nat} {s : State} (hn : 2 ≤ n) (hi : i < n) (hs : Valid n s) :
    edgeBit n (exchange s) i = !(edgeBit n s i) := by
  have hnext : (i + 1) % n < n := Nat.mod_lt _ (by omega)
  have hmi := hs.placement_mem.mpr hi
  have hmn := hs.placement_mem.mpr hnext
  cases hb : edgeBit n s i with
  | false =>
    have hr := (edgeBit_false_iff hn hi hs).mp hb
    change edgeBit n (exchange s) i = true
    simp only [edgeBit, placement_exchange, decide_eq_true_eq]
    exact (idxOf_reverse_lt_iff hs.placement_nodup hmi hmn).mpr hr
  | true =>
    have hr : (placement s).idxOf i < (placement s).idxOf ((i + 1) % n) := by
      simpa only [edgeBit, decide_eq_true_eq] using hb
    change edgeBit n (exchange s) i = false
    apply (edgeBit_false_iff hn hi hs.exchange).mpr
    rw [placement_exchange]
    exact (idxOf_reverse_lt_iff hs.placement_nodup hmn hmi).mpr hr

theorem orientation_exchange_not {n : Nat} {s : State} (hn : 2 ≤ n) (hs : Valid n s) :
    orientation n (exchange s) = (orientation n s).map Bool.not := by
  apply List.ext_getElem
  · simp only [orientation_length, List.length_map]
  · intro i hi hj
    have hin : i < n := by simpa only [orientation_length] using hi
    simpa only [List.getElem_map, orientation_getElem hin] using edgeBit_exchange_not hn hin hs

theorem EdgeBitFlip.exchange {n i : Nat} {s t : State} (hn : 2 ≤ n) (hi : i < n)
    (hs : Valid n s) (ht : Valid n t) (h : EdgeBitFlip n s t i) :
    EdgeBitFlip n (exchange s) (exchange t) i := by
  constructor
  · intro j hj hji
    rw [edgeBit_exchange_not hn hj hs, edgeBit_exchange_not hn hj ht, h.1 j hj hji]
  · rw [edgeBit_exchange_not hn hi hs, edgeBit_exchange_not hn hi ht, h.2]

theorem DirectedPathFlip.circularFlip {n w : Nat} {s t : State}
    (hn : 3 ≤ n) (hs : Valid n s) (ht : Valid n t) (h : DirectedPathFlip n w s t) :
    CircularWord.CircularFlip w (orientation n s) (orientation n t) := by
  have hne := h.orientation_ne hs ht
  obtain ⟨p, u, v, hp, hpath, hlen, he, _⟩ := h
  have hpop := hs.placement_perm.length_eq
  have hsize := hp.length_le
  have hw : w + 1 < n := by simp only [List.length_append, List.length_cons, List.length_nil, hlen,
    List.length_range] at hsize hpop; omega
  obtain ⟨a, ha, harc⟩ := cycle_path_is_arc (by simp) (hs.placement_nodup.sublist hp)
    (fun x hx => hs.placement_mem.mp (hp.subset hx)) hpath
  have hplen : (p ++ [u, v]).length - 1 = w + 1 := by simp [hlen]
  rw [hplen] at harc
  rcases harc with harc | harc
  · have hsub : (cycleArc n a (w + 1)).Sublist (placement s) := by simpa only [← harc] using hp
    have hends := List.append_inj_right (harc.trans (cycleArc_last_two n a w))
      (by simp [hlen])
    obtain ⟨hu, hv⟩ : u = (a + w) % n ∧ v = (a + w + 1) % n := by simpa using hends
    subst u
    subst v
    have her : EdgeEquiv (eraseEdge (cycleAdjacent n) ((a + w) % n)
        (((a + w) % n + 1) % n)) (placement s) (placement t) := by
      simpa only [Nat.mod_add_mod] using he
    have hf := edgeBitFlip_of_erase_of_ne hn (Nat.mod_lt _ (by omega)) her hne
    have hfr := (rotatedFlipAt_iff_edgeBitFlip a (by omega : w < n)).mpr hf
    have hbits := (cycleArc_forward_sublist_iff (by omega) hs).mp hsub
    have hprefix := orientation_prefix_eq a hw.le hbits
    exact ⟨a, (show CircularWord.PrefixFlip w ((orientation n s).rotate a) ((orientation n t).rotate a) from
      ⟨true, _, hprefix, Or.inr (CircularWord.flipAt_last_prefix hprefix hfr)⟩).linearFlip⟩
  · have hsub : (cycleArc n a (w + 1)).reverse.Sublist (placement s) := by
      simpa only [← harc, List.reverse_reverse] using hp
    obtain ⟨r, _, hr⟩ := cycleArc_first_two ha w
    have hends : v :: u :: p.reverse = a :: ((a + 1) % n) :: r := by
      simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append] using harc.trans hr
    have hv := (List.cons.inj hends).1
    have hu := (List.cons.inj (List.cons.inj hends).2).1
    subst v
    subst u
    have her : EdgeEquiv (eraseEdge (cycleAdjacent n) a ((a + 1) % n)) (placement s) (placement t) := by
      simpa only [EdgeEquiv, eraseEdge, Bool.or_comm] using he
    have hf := edgeBitFlip_of_erase_of_ne hn ha her hne
    have hfr := (rotatedFlipAt_iff_edgeBitFlip (s := s) (t := t) a (by omega : 0 < n)).mpr
      (by simpa only [Nat.add_zero, Nat.mod_eq_of_lt ha] using hf)
    have hbits := (cycleArc_backward_sublist_iff (by omega) hs).mp hsub
    have hprefix := orientation_prefix_eq a hw.le hbits
    exact ⟨a, (show CircularWord.PrefixFlip w ((orientation n s).rotate a) ((orientation n t).rotate a) from
      ⟨false, _, hprefix, Or.inl (CircularWord.flipAt_first_prefix hprefix hfr)⟩).linearFlip⟩

theorem PathFlip.circularFlip {n w : Nat} {s t : State}
    (hn : 3 ≤ n) (hs : Valid n s) (ht : Valid n t) (h : PathFlip n w s t) :
    CircularWord.CircularFlip w (orientation n s) (orientation n t) := by
  rcases h with h | h
  · exact h.circularFlip hn hs ht
  · have hh := h.circularFlip hn hs.exchange ht.exchange
    rw [orientation_exchange_not (by omega) hs, orientation_exchange_not (by omega) ht] at hh
    exact CircularWord.CircularFlip.not_iff.mp hh

theorem prefixFlip_pathFlip {n w a : Nat} {s t : State}
    (hn : 3 ≤ n) (ha : a < n) (hs : Valid n s) (ht : Valid n t)
    (h : CircularWord.PrefixFlip w ((orientation n s).rotate a) ((orientation n t).rotate a)) :
    PathFlip n w s t := by
  obtain ⟨b, tail, hsource, htarget⟩ := h
  have hbits := orientation_prefix_bits a hsource
  rcases htarget with hfirst | hlast
  · have hf : CircularWord.FlipAt ((orientation n s).rotate a) ((orientation n t).rotate a) 0 :=
      ⟨[], List.replicate w b ++ tail, b, rfl,
        by simpa only [List.replicate_succ, List.cons_append] using hsource, hfirst⟩
    have hbit : EdgeBitFlip n s t a := by
      simpa only [Nat.add_zero, Nat.mod_eq_of_lt ha] using
        (rotatedFlipAt_iff_edgeBitFlip a (by omega : 0 < n)).mp hf
    cases b with
    | false =>
      exact Or.inl (first_arc_directedPathFlip hn ha hs ht
        ((cycleArc_backward_sublist_iff (by omega) hs).mpr hbits.2) hbit)
    | true =>
      have hsub := (cycleArc_forward_sublist_iff (by omega) hs).mpr hbits.2
      have hex : (cycleArc n a (w + 1)).reverse.Sublist (placement (exchange s)) := by
        simpa only [placement_exchange] using hsub.reverse
      exact Or.inr (first_arc_directedPathFlip hn ha hs.exchange ht.exchange hex
        (hbit.exchange (by omega) ha hs ht))
  · have hf : CircularWord.FlipAt ((orientation n s).rotate a) ((orientation n t).rotate a) w :=
      ⟨List.replicate w b, tail, b, List.length_replicate,
        by simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using hsource, hlast⟩
    have hbit := (rotatedFlipAt_iff_edgeBitFlip (s := s) (t := t) a
      (by have hh := hbits.1; omega : w < n)).mp hf
    cases b with
    | true =>
      exact Or.inl (last_arc_directedPathFlip hn hs ht
        ((cycleArc_forward_sublist_iff (by omega) hs).mpr hbits.2) hbit)
    | false =>
      have hsub := (cycleArc_backward_sublist_iff (by omega) hs).mpr hbits.2
      have hex : (cycleArc n a (w + 1)).Sublist (placement (exchange s)) := by
        simpa only [placement_exchange, List.reverse_reverse] using hsub.reverse
      exact Or.inr (last_arc_directedPathFlip hn hs.exchange ht.exchange hex
        (hbit.exchange (by omega) (Nat.mod_lt _ (by omega)) hs ht))

theorem circularFlip_pathFlip {n w : Nat} {s t : State}
    (hn : 3 ≤ n) (hs : Valid n s) (ht : Valid n t)
    (h : CircularWord.CircularFlip w (orientation n s) (orientation n t)) : PathFlip n w s t := by
  obtain ⟨k, hk⟩ := CircularWord.circularFlip_iff_prefix.mp h
  have hqs : (orientation n s).rotate (k % n) = (orientation n s).rotate k := by
    simpa only [orientation_length] using List.rotate_mod (orientation n s) k
  have hqt : (orientation n t).rotate (k % n) = (orientation n t).rotate k := by
    simpa only [orientation_length] using List.rotate_mod (orientation n t) k
  exact prefixFlip_pathFlip (a := k % n) hn (Nat.mod_lt k (by omega)) hs ht
    (by simpa only [hqs, hqt] using hk)

theorem pathFlip_iff_circularFlip {n w : Nat} {s t : State}
    (hn : 3 ≤ n) (hs : Valid n s) (ht : Valid n t) :
    PathFlip n w s t ↔ CircularWord.CircularFlip w (orientation n s) (orientation n t) :=
  ⟨PathFlip.circularFlip hn hs ht, circularFlip_pathFlip hn hs ht⟩

/-- The complete local-move equivalence for actual queue configurations and
the circular binary flip graph. The initiating completion is not a swap. -/
theorem orientationStep_iff_circularFlip {n w : Nat} {s t : State}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hs : Valid n s) (ht : Valid n t) :
    (CycleState.OrientationStep n w (orientation n s) (orientation n t) ∧
      orientation n s ≠ orientation n t) ↔
      CircularWord.CircularFlip w (orientation n s) (orientation n t) := by
  rw [orientationStep_iff_pathFlip hn hw hs ht, pathFlip_iff_circularFlip hn hs ht]

end OddCycle
