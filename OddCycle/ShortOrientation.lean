import OddCycle.OrientationQuotient
import OddCycle.UnlimitedCarry
import OddCycle.GeneralHeight

/-! Short placement orders are closed under the actual limited dynamics.
The proof applies to every finite cycle and every replacement budget. -/

namespace OddCycle

/-- Every directed adjacency chain in a word has at most `w` edges. -/
def PathsBounded (adj : Nat → Nat → Bool) (w : Nat) (q : Queue) : Prop :=
  ∀ p, p.Sublist q → pathEdges adj p = true → p.length ≤ w + 1

theorem PathsBounded.sublist {adj : Nat → Nat → Bool} {w : Nat} {q r : Queue}
    (h : PathsBounded adj w q) (hr : r.Sublist q) : PathsBounded adj w r :=
  fun p hp he => h p (hp.trans hr) he

theorem carry_eq_unlimited_of_paths {adj : Nat → Nat → Bool}
    (q : Queue) (job budget : Nat)
    (hbound : ∀ p, p.Sublist q → pathEdges adj (job :: p) = true → p.length ≤ budget) :
    carry adj budget job q = unlimitedCarry adj job q := by
  induction q generalizing job budget with
  | nil => rfl
  | cons x xs ih =>
    by_cases hzero : budget = 0
    · have hno : ∀ y ∈ x :: xs, adj job y = false := by
        intro y hy
        by_contra hn
        have ha : adj job y = true := by cases h : adj job y <;> simp_all
        have hp := hbound [y] (List.singleton_sublist.mpr hy) (by simp [pathEdges, ha])
        simp only [List.length_singleton, hzero] at hp
        omega
      have hu := carry_of_no_adj (adj := adj) (x :: xs).length job (x :: xs) hno
      rw [carry_eq_unlimited adj _ job _ (Nat.le_refl _)] at hu
      rw [carry_of_no_adj budget job _ hno, hu]
    · by_cases ha : adj job x = true
      · have hb : ∀ p, p.Sublist xs → pathEdges adj (x :: p) = true → p.length ≤ budget - 1 := by
          intro p hp he
          have hh := hbound (x :: p) (hp.cons_cons x) (by simp [pathEdges, ha, he])
          simp only [List.length_cons] at hh
          omega
        simp only [carry, hzero, if_false, ha, if_true, unlimitedCarry, ih x (budget - 1) hb]
      · have hb : ∀ p, p.Sublist xs → pathEdges adj (job :: p) = true → p.length ≤ budget :=
          fun p hp he => hbound p (hp.cons x) he
        simp [carry, unlimitedCarry, hzero, ha, ih job budget hb]

theorem carry_short_edgeEquiv {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) {w : Nat} {job : Nat} {q : Queue}
    (hb : PathsBounded adj w (job :: q)) :
    EdgeEquiv adj (job :: q) ((carry adj w job q).1 ++ [(carry adj w job q).2]) := by
  have he := carry_eq_unlimited_of_paths q job w (by
    intro p hp hpath
    have hh := hb (job :: p) (hp.cons_cons job) hpath
    simp only [List.length_cons] at hh
    omega)
  rw [he]
  exact unlimitedCarry_edgeEquiv hsym q job

theorem complete_short_edgeEquiv {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) {w pos : Nat} {q rest : Queue}
    {departed initiating : Nat} (hb : PathsBounded adj w q)
    (he : complete adj w q pos = some (rest, departed, initiating)) :
    EdgeEquiv adj q (rest ++ [departed]) := by
  induction q generalizing pos rest departed initiating with
  | nil => simp [complete] at he
  | cons a q ih =>
    cases pos with
    | zero =>
      simp only [complete, Option.some.injEq, Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl, rfl⟩
      exact carry_short_edgeEquiv hsym hb
    | succ pos =>
      cases hc : complete adj w q pos with
      | none => simp [complete, hc] at he
      | some result =>
        obtain ⟨r, d, i⟩ := result
        simp [complete, hc] at he
        rcases he with ⟨rfl, rfl, rfl⟩
        exact (ih (hb.sublist (List.sublist_cons_self a q)) hc).cons a

theorem pathEdges_reverse {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) (q : Queue) :
    pathEdges adj q.reverse = true ↔ pathEdges adj q = true := by
  simp only [pathEdges_iff_isChain, List.isChain_reverse]
  simp only [hsym]

theorem PathsBounded.reverse {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) {w : Nat} {q : Queue}
    (hb : PathsBounded adj w q) : PathsBounded adj w q.reverse := by
  intro p hp he
  have hsub : p.reverse.Sublist q := by simpa using hp.reverse
  simpa using hb p.reverse hsub ((pathEdges_reverse hsym p).mpr he)

theorem pathsBounded_iff_height {n w : Nat} {s : State} :
    PathsBounded (cycleAdjacent n) w (placement s) ↔ height n s ≤ w := by
  constructor
  · intro hb
    apply foldl_max_le (Nat.zero_le _)
    intro k hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    obtain ⟨hp, he⟩ := List.mem_filter.mp hp
    have hh := hb p (List.mem_sublists.mp hp) he
    omega
  · intro hh p hp he
    have h := path_length_le_height hp he
    omega

theorem height_exchange_le {n w : Nat} {s : State} (hs : height n s ≤ w) :
    height n (exchange s) ≤ w := by
  apply pathsBounded_iff_height.mp
  rw [placement_exchange]
  exact (pathsBounded_iff_height.mpr hs).reverse (cycleAdjacent_symm n)

theorem transition_first_short_orientation {n w pos initiating : Nat} {s t : State}
    (hs : height n s ≤ w)
    (he : transition (cycleAdjacent n) w s false pos = some (t, initiating)) :
    orientation n s = orientation n t := by
  cases hc : complete (cycleAdjacent n) w s.1 pos with
  | none => simp [transition, hc] at he
  | some result =>
    obtain ⟨r, d, i⟩ := result
    simp [transition, hc] at he
    rcases he with ⟨rfl, rfl⟩
    have hb := (pathsBounded_iff_height.mpr hs).sublist
      (show s.1.Sublist (placement s) from List.sublist_append_left _ _)
    have hh := complete_short_edgeEquiv (cycleAdjacent_symm n) hb hc
    apply EdgeEquiv.orientation_eq
    simpa only [placement, List.reverse_append, List.reverse_singleton, List.append_assoc,
      List.singleton_append] using hh.append_right s.2.reverse

theorem transition_short_orientation {n w pos initiating : Nat} {s t : State} {side : Bool}
    (hn : 0 < n) (hv : Valid n s) (hs : height n s ≤ w)
    (he : transition (cycleAdjacent n) w s side pos = some (t, initiating)) :
    orientation n s = orientation n t := by
  cases side with
  | false => exact transition_first_short_orientation hs he
  | true =>
    have he' := transition_exchange he
    have hh := transition_first_short_orientation (height_exchange_le hs) he'
    have ht := transition_valid hv he
    simpa only [exchange_exchange] using orientation_exchange_eq hn hv.exchange ht.exchange hh

theorem path_sublist_of_orientation_eq {n : Nat} {s t : State} {p : Queue}
    (hs : Valid n s) (ht : Valid n t) (ho : orientation n s = orientation n t)
    (hp : p.Sublist (placement s)) (he : pathEdges (cycleAdjacent n) p = true) :
    p.Sublist (placement t) := by
  have hordered : (placement s).Pairwise
      (fun a b => (placement s).idxOf a < (placement s).idxOf b) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [hs.placement_nodup.idxOf_getElem i hi,
      hs.placement_nodup.idxOf_getElem j hj] using hij
  have hpair := List.pairwise_iff_getElem.mp (hordered.sublist hp)
  have hchain := List.isChain_iff_getElem.mp ((pathEdges_iff_isChain _ _).mp he)
  have hnew : p.IsChain (fun a b => (placement t).idxOf a < (placement t).idxOf b) := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    have hi' : i < p.length := by omega
    have ha := hs.placement_mem.mp (hp.subset (List.getElem_mem hi'))
    have hb := hs.placement_mem.mp (hp.subset (List.getElem_mem hi))
    exact (orientation_before_iff hs ht ho ha hb (hchain i hi)).mp
      (hpair i (i + 1) hi' hi (by omega))
  letI : Trans (fun a b => (placement t).idxOf a < (placement t).idxOf b)
      (fun a b => (placement t).idxOf a < (placement t).idxOf b)
      (fun a b => (placement t).idxOf a < (placement t).idxOf b) := ⟨Nat.lt_trans⟩
  exact sublist_of_idxOf_pairwise ht.placement_nodup
    (fun a ha => ht.placement_mem.mpr (hs.placement_mem.mp (hp.subset ha))) hnew.pairwise

theorem height_eq_of_orientation_eq {n : Nat} {s t : State}
    (hs : Valid n s) (ht : Valid n t) (ho : orientation n s = orientation n t) :
    height n s = height n t := by
  have hle {a b : State} (ha : Valid n a) (hb : Valid n b)
      (ho : orientation n a = orientation n b) : height n a ≤ height n b := by
    apply pathsBounded_iff_height.mp
    intro p hp he
    exact (pathsBounded_iff_height.mpr (Nat.le_refl (height n b))) p
      (path_sublist_of_orientation_eq ha hb ho hp he) he
  exact le_antisymm (hle hs ht ho) (hle ht hs ho.symm)

/-- Exactly the original orientation is reachable from a short state. -/
theorem short_reachable_iff {n w : Nat} (hn : 0 < n) {s t : State}
    (hs : Valid n s) (ht : Valid n t) (hshort : height n s ≤ w) :
    EventReachable (cycleAdjacent n) w s t ↔ orientation n s = orientation n t := by
  constructor
  · intro h
    clear ht
    have hp : Valid n t ∧ orientation n s = orientation n t := by
      induction h with
      | refl => exact ⟨hs, rfl⟩
      | @tail a b _ hab ih =>
        obtain ⟨side, pos, job, he⟩ := hab
        have ha : height n a ≤ w := by
          rw [← height_eq_of_orientation_eq hs ih.1 ih.2]
          exact hshort
        exact ⟨transition_valid ih.1 he, ih.2.trans (transition_short_orientation hn ih.1 ha he)⟩
    exact hp.2
  · exact reachable_of_orientation_eq hs ht

theorem short_terminal {n w : Nat} (hn : 0 < n) (s : CycleState n)
    (hs : height n s.val ≤ w) : ReachabilityQuotient.Terminal (CycleState.Step n w) s := by
  intro t h
  apply CycleState.event_reachable_iff.mpr
  have ho := (short_reachable_iff hn s.property t.property hs).mp
    (CycleState.event_reachable_iff.mp h)
  exact reachable_of_orientation_eq t.property s.property ho.symm

theorem height_le_population {n : Nat} {s : State} (hs : Valid n s) : height n s ≤ n - 1 := by
  apply foldl_max_le (Nat.zero_le _)
  intro k hk
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  have hlen := (List.mem_sublists.mp (List.mem_filter.mp hp).1).length_le
  have hslen := hs.placement_perm.length_eq
  simp only [List.length_range] at hslen
  omega

theorem large_budget_preserves_orientation {n w pos initiating : Nat} {s t : State} {side : Bool}
    (hn : 0 < n) (hs : Valid n s) (hw : n - 1 ≤ w)
    (he : transition (cycleAdjacent n) w s side pos = some (t, initiating)) :
    orientation n s = orientation n t :=
  transition_short_orientation hn hs ((height_le_population hs).trans hw) he

end OddCycle
