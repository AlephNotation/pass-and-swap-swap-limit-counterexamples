import OddCycle.CyclePathRealization
import OddCycle.OrientationQuotient

/-! The exact operational orientation quotient, expressed using directed
cycle paths. Queue exchange supplies paths in the reverse placement. -/

namespace OddCycle

theorem orientation_edgeEquiv {n : Nat} {s t : State}
    (hs : Valid n s) (ht : Valid n t) (ho : orientation n s = orientation n t) :
    EdgeEquiv (cycleAdjacent n) (placement s) (placement t) := by
  apply WordReachable.edgeEquiv (cycleAdjacent_symm n)
  apply word_reachable_of_before (cycleAdjacent_symm n) hs.placement_nodup
    (hs.placement_perm.trans ht.placement_perm.symm)
  intro a ha b hb hab
  exact orientation_before_iff hs ht ho (hs.placement_mem.mp ha) (hs.placement_mem.mp hb) hab

theorem orientation_eq_of_erase_and_before {n u v : Nat} {s t : State}
    (hn : 0 < n)
    (he : EdgeEquiv (eraseEdge (cycleAdjacent n) u v) (placement s) (placement t))
    (hs : (placement s).idxOf v < (placement s).idxOf u)
    (ht : (placement t).idxOf v < (placement t).idxOf u) :
    orientation n s = orientation n t := by
  apply orientation_eq_of_except hn
    (show (placement s).idxOf u < (placement s).idxOf v ↔
      (placement t).idxOf u < (placement t).idxOf v by omega)
    (show (placement s).idxOf v < (placement s).idxOf u ↔
      (placement t).idxOf v < (placement t).idxOf u from iff_of_true hs ht)
  intro a b _ _ hab hne
  apply he.before_iff
  simp [eraseEdge, hab]
  tauto

/-- A prescribed orientation change, with its enabling path in placement
order and its last edge reversed. -/
def DirectedPathFlip (n w : Nat) (s t : State) : Prop :=
  ∃ p u v, (p ++ [u, v]).Sublist (placement s) ∧
    pathEdges (cycleAdjacent n) (p ++ [u, v]) = true ∧ p.length = w ∧
    EdgeEquiv (eraseEdge (cycleAdjacent n) u v) (placement s) (placement t) ∧
    (placement t).idxOf v < (placement t).idxOf u

def PathFlip (n w : Nat) (s t : State) : Prop :=
  DirectedPathFlip n w s t ∨ DirectedPathFlip n w (exchange s) (exchange t)

theorem DirectedPathFlip.orientation_ne {n w : Nat} {s t : State}
    (hs : Valid n s) (ht : Valid n t) (h : DirectedPathFlip n w s t) :
    orientation n s ≠ orientation n t := by
  obtain ⟨p, u, v, hp, hpath, _, _, hrev⟩ := h
  have huv := before_of_pair_sublist hs.placement_nodup
    ((List.sublist_append_right p [u, v]).trans hp)
  have hu : u < n := hs.placement_mem.mp (hp.subset (by simp))
  have hv : v < n := hs.placement_mem.mp (hp.subset (by simp))
  have hadj := (List.isChain_append_cons_cons.mp
    ((pathEdges_iff_isChain _ _).mp hpath)).2.1
  intro ho
  have hh := (orientation_before_iff hs ht ho hu hv hadj).mp huv
  omega

theorem PathFlip.orientation_ne {n w : Nat} {s t : State}
    (hn : 0 < n) (hs : Valid n s) (ht : Valid n t) (h : PathFlip n w s t) :
    orientation n s ≠ orientation n t := by
  rcases h with h | h
  · exact h.orientation_ne hs ht
  · exact fun he => h.orientation_ne hs.exchange ht.exchange
      (orientation_exchange_eq hn hs ht he)

theorem DirectedPathFlip.realize {n w : Nat} {s t : State}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hs : Valid n s) (_ht : Valid n t)
    (h : DirectedPathFlip n w s t) :
    CycleState.OrientationStep n w (orientation n s) (orientation n t) := by
  obtain ⟨p, u, v, hp, hpath, hlen, he, hrev⟩ := h
  obtain ⟨r, rest, departed, initiating, pos, hr, hc, her, hrr⟩ :=
    cycle_path_realize_flip hn hw hs.placement_nodup
      (fun x hx => hs.placement_mem.mp hx) hp hpath hlen
  have hv : Valid n (r, []) := by
    simpa only [Valid, List.append_nil] using hr.perm.symm.trans hs.placement_perm
  have htransition : transition (cycleAdjacent n) w (r, []) false pos =
      some ((rest, [departed]), initiating) := by simp [transition, hc]
  have hvt := transition_valid hv htransition
  have hsource : orientation n (r, []) = orientation n s := by
    apply EdgeEquiv.orientation_eq
    simpa only [placement, List.reverse_nil, List.append_nil] using
      (hr.edgeEquiv (cycleAdjacent_symm n)).symm
  have htarget : orientation n (rest, [departed]) = orientation n t := by
    apply orientation_eq_of_erase_and_before (by omega)
    · simpa only [placement, List.reverse_singleton] using her.symm.trans he
    · exact hrr
    · exact hrev
  exact ⟨⟨(r, []), hv⟩, ⟨(rest, [departed]), hvt⟩, hsource, htarget,
    false, pos, initiating, htransition⟩

theorem CycleState.OrientationStep.exchange {n w : Nat} {s t : State}
    (hn : 0 < n) (hs : Valid n s) (ht : Valid n t)
    (h : CycleState.OrientationStep n w (orientation n s) (orientation n t)) :
    CycleState.OrientationStep n w (orientation n (exchange s)) (orientation n (exchange t)) := by
  obtain ⟨a, b, ha, hb, he⟩ := h
  exact ⟨⟨OddCycle.exchange a.val, a.property.exchange⟩, ⟨OddCycle.exchange b.val, b.property.exchange⟩,
    orientation_exchange_eq hn a.property hs ha,
    orientation_exchange_eq hn b.property ht hb, he.exchange⟩

theorem PathFlip.realize {n w : Nat} {s t : State}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hs : Valid n s) (ht : Valid n t)
    (h : PathFlip n w s t) :
    CycleState.OrientationStep n w (orientation n s) (orientation n t) := by
  rcases h with h | h
  · exact h.realize hn hw hs ht
  · simpa only [exchange_exchange] using
      (h.realize hn hw hs.exchange ht.exchange).exchange (by omega) hs.exchange ht.exchange

theorem first_transition_pathFlip {n w pos initiating : Nat} {s t : State}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hs : Valid n s)
    (he : transition (cycleAdjacent n) w s false pos = some (t, initiating))
    (hne : orientation n s ≠ orientation n t) : DirectedPathFlip n w s t := by
  obtain ⟨p, u, v, hp, hpath, hlen, _, her⟩ := first_transition_changed_path hn hw hs he hne
  refine ⟨p, u, v, hp, hpath, hlen, her, ?_⟩
  have hbefore := before_of_pair_sublist hs.placement_nodup
    ((List.sublist_append_right p [u, v]).trans hp)
  have huv : u ≠ v := by intro hh; subst v; omega
  have ht := transition_valid hs he
  have hu : u ∈ placement t := ht.placement_mem.mpr (hs.placement_mem.mp (hp.subset (by simp)))
  have hind : (placement t).idxOf u ≠ (placement t).idxOf v :=
    fun hh => huv ((List.idxOf_inj hu).mp hh)
  by_contra hnot
  have hafter : (placement t).idxOf u < (placement t).idxOf v := by omega
  apply hne
  apply orientation_eq_of_erase_and_before (u := v) (v := u) (by omega) ?_ hbefore hafter
  simpa only [EdgeEquiv, eraseEdge, Bool.or_comm] using her

theorem transition_pathFlip {n w pos initiating : Nat} {s t : State} {side : Bool}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hs : Valid n s)
    (he : transition (cycleAdjacent n) w s side pos = some (t, initiating))
    (hne : orientation n s ≠ orientation n t) : PathFlip n w s t := by
  cases side with
  | false => exact Or.inl (first_transition_pathFlip hn hw hs he hne)
  | true =>
    apply Or.inr
    apply first_transition_pathFlip hn hw hs.exchange (transition_exchange he)
    intro hh
    apply hne
    simpa only [exchange_exchange] using orientation_exchange_eq (by omega)
      hs.exchange (transition_valid hs he).exchange hh

theorem DirectedPathFlip.congr {n w : Nat} {a b s t : State}
    (ha : Valid n a) (hb : Valid n b) (hs : Valid n s) (ht : Valid n t)
    (has : orientation n a = orientation n s) (hbt : orientation n b = orientation n t)
    (h : DirectedPathFlip n w a b) : DirectedPathFlip n w s t := by
  obtain ⟨p, u, v, hp, hpath, hlen, he, hrev⟩ := h
  have hu := ha.placement_mem.mp (hp.subset (by simp : u ∈ p ++ [u, v]))
  have hv := ha.placement_mem.mp (hp.subset (by simp : v ∈ p ++ [u, v]))
  have hadj := (List.isChain_append_cons_cons.mp
    ((pathEdges_iff_isChain _ _).mp hpath)).2.1
  exact ⟨p, u, v, path_sublist_of_orientation_eq ha hs has hp hpath, hpath, hlen,
    ((orientation_edgeEquiv ha hs has).symm.erase u v).trans
      (he.trans ((orientation_edgeEquiv hb ht hbt).erase u v)),
    (orientation_before_iff hb ht hbt hv hu
      (by simpa only [cycleAdjacent_symm n] using hadj)).mp hrev⟩

theorem PathFlip.congr {n w : Nat} {a b s t : State}
    (hn : 0 < n) (ha : Valid n a) (hb : Valid n b) (hs : Valid n s) (ht : Valid n t)
    (has : orientation n a = orientation n s) (hbt : orientation n b = orientation n t)
    (h : PathFlip n w a b) : PathFlip n w s t := by
  rcases h with h | h
  · exact Or.inl (h.congr ha hb hs ht has hbt)
  · exact Or.inr (h.congr ha.exchange hb.exchange hs.exchange ht.exchange
      (orientation_exchange_eq hn ha hs has) (orientation_exchange_eq hn hb ht hbt))

/-- Exact nontrivial local-move theorem for the actual operational quotient.
It is an equivalence about one quotient edge, not merely eventual reachability. -/
theorem orientationStep_iff_pathFlip {n w : Nat} {s t : State}
    (hn : 3 ≤ n) (hw : 1 ≤ w) (hs : Valid n s) (ht : Valid n t) :
    (CycleState.OrientationStep n w (orientation n s) (orientation n t) ∧
      orientation n s ≠ orientation n t) ↔ PathFlip n w s t := by
  constructor
  · rintro ⟨⟨a, b, ha, hb, side, pos, initiating, he⟩, hne⟩
    have hab : orientation n a.val ≠ orientation n b.val := by
      intro hh
      exact hne (ha.symm.trans (hh.trans hb))
    exact (transition_pathFlip hn hw a.property he hab).congr (by omega)
      a.property b.property hs ht ha hb
  · intro h
    exact ⟨h.realize hn hw hs ht, h.orientation_ne (by omega) hs ht⟩

end OddCycle
