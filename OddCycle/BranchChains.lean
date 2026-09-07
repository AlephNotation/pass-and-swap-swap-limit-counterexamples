import OddCycle.GeneralHeight
import OddCycle.BalancedSymmetry
import OddCycle.Interleavings

/-! Balanced placements are precisely interleavings of the two branch
interiors between their common source and sink. -/

namespace OddCycle

def longInterior (w source : Nat) (forward : Bool) : Queue :=
  (List.range w).map (fun j => cycleLabel (2 * w + 1) source forward (j + 1))

def shortInterior (w source : Nat) (forward : Bool) : Queue :=
  (List.range (w - 1)).map (fun j => cycleLabel (2 * w + 1) source forward (2 * w + 1 - (j + 1)))

def shortBranch (w source : Nat) (forward : Bool) : Queue :=
  (List.range (w + 1)).map (cycleLabel (2 * w + 1) source (!forward))

theorem cycleLabel_zero {n source : Nat} (hs : source < n) (forward : Bool) :
    cycleLabel n source forward 0 = source := by
  cases forward <;> simp [cycleLabel, Nat.mod_eq_of_lt hs]

theorem cycleLabel_not {n source k : Nat} (hk : k < n) (forward : Bool) :
    cycleLabel n source (!forward) k = cycleLabel n source forward (reflect n k) := by
  rw [cycleLabel_eq_rotate, cycleLabel_eq_rotate]
  cases forward
  · simpa using congrArg (rotate n source) (reflect_involutive hk).symm
  · rfl

theorem branchWord_eq_interiors (w source : Nat) (forward : Bool) :
    branchWord w source forward = source ::
      (longInterior w source forward ++ shortInterior w source forward) ++
        [cycleLabel (2 * w + 1) source forward (w + 1)] := by
  simp [branchWord, longInterior, shortInterior, cycleLabel, List.append_assoc]

theorem longBranch_eq_interiors {w source : Nat} (hs : source < 2 * w + 1) (forward : Bool) :
    longBranch w source forward = source :: longInterior w source forward ++
      [cycleLabel (2 * w + 1) source forward (w + 1)] := by
  unfold longBranch
  rw [show w + 2 = (w + 1) + 1 by omega, List.range_succ, List.map_append,
    List.range_succ_eq_map]
  simp [longInterior, cycleLabel_zero hs, List.map_map, Function.comp_def]

theorem shortBranch_eq_interiors {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (forward : Bool) :
    shortBranch w source forward = source :: shortInterior w source forward ++
      [cycleLabel (2 * w + 1) source forward (w + 1)] := by
  have hr : List.range w = 0 :: (List.range (w - 1)).map (· + 1) := by
    conv_lhs => rw [show w = (w - 1) + 1 by omega, List.range_succ_eq_map]
  rw [shortBranch, List.range_succ, List.map_append, hr]
  simp only [List.map_cons, List.map_map, cycleLabel_zero hs, List.cons_append]
  apply congrArg (List.cons source)
  apply congrArg₂ List.append
  · apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    simp only [Function.comp_apply]
    rw [cycleLabel_not (show j + 1 < 2 * w + 1 by omega) forward,
      reflect_eq (show j + 1 < 2 * w + 1 by omega), if_neg (by omega)]
  · apply congrArg List.singleton
    rw [cycleLabel_not (show w < 2 * w + 1 by omega) forward,
      reflect_eq (show w < 2 * w + 1 by omega), if_neg (by omega)]
    congr 1
    omega

theorem shortBranch_sublist {w source : Nat} {s : State} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (hv : Valid (2 * w + 1) s) (forward : Bool)
    (hori : orientation (2 * w + 1) s = orientation (2 * w + 1) (branchState w source forward)) :
    (shortBranch w source forward).Sublist (placement s) := by
  have hn : 0 < 2 * w + 1 := by omega
  apply sublist_of_idxOf_pairwise hv.placement_nodup
  · intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact hv.placement_mem.mpr (cycleLabel_lt hn (!forward))
  · letI : Trans (fun a b => (placement s).idxOf a < (placement s).idxOf b)
        (fun a b => (placement s).idxOf a < (placement s).idxOf b)
        (fun a b => (placement s).idxOf a < (placement s).idxOf b) := ⟨Nat.lt_trans⟩
    apply List.IsChain.pairwise
    rw [shortBranch, List.isChain_map, List.isChain_range_succ]
    intro k hk
    have ha : k < 2 * w + 1 := by omega
    have hb : k + 1 < 2 * w + 1 := by omega
    have hadj : cycleAdjacent (2 * w + 1) k (k + 1) = true := by
      simp [cycleAdjacent, Nat.mod_eq_of_lt hb]
    apply (orientation_before_iff hv (branchState_valid hw hs forward) hori
      (cycleLabel_lt hn (!forward)) (cycleLabel_lt hn (!forward))
      ((cycleLabel_adj_iff hs ha hb (!forward)).mpr hadj)).mpr
    simp only [placement, branchState, List.reverse_nil, List.append_nil]
    rw [cycleLabel_not ha forward, cycleLabel_not hb forward,
      branchWord_idxOf_label hw hs (show reflect (2 * w + 1) k < 2 * w + 1 from Nat.mod_lt _ hn) forward,
      branchWord_idxOf_label hw hs (show reflect (2 * w + 1) (k + 1) < 2 * w + 1 from Nat.mod_lt _ hn) forward,
      reflect_eq ha, reflect_eq hb]
    by_cases hz : k = 0
    · subst k
      simp only [Nat.zero_add, if_neg (by omega : 1 ≠ 0)]
      simp [foldedIndex, show ¬2 * w ≤ w by omega]
      omega
    · have hx : ¬2 * w + 1 - k ≤ w := by omega
      have hy : ¬2 * w + 1 - (k + 1) ≤ w := by omega
      simp only [if_neg hz, if_neg (by omega : k + 1 ≠ 0), foldedIndex,
        if_neg hx, if_neg hy]
      omega

theorem placement_interleaving_of_orientation {w source : Nat} {s : State}
    (hw : 2 ≤ w) (hs : source < 2 * w + 1) (hv : Valid (2 * w + 1) s) (forward : Bool)
    (hori : orientation (2 * w + 1) s = orientation (2 * w + 1) (branchState w source forward)) :
    ∃ mid ∈ interleavings (longInterior w source forward) (shortInterior w source forward),
      placement s = source :: mid ++ [cycleLabel (2 * w + 1) source forward (w + 1)] := by
  have hcanonical := branchState_valid hw hs forward
  have hn : (branchWord w source forward).Nodup := by
    simpa [placement, branchState] using hcanonical.placement_nodup
  have hp : (placement s).Perm (branchWord w source forward) := by
    simpa [placement, branchState] using hv.placement_perm.trans hcanonical.placement_perm.symm
  rw [branchWord_eq_interiors] at hn hp
  apply bookended_interleavings hn hp
  · simpa only [longBranch_eq_interiors hs forward] using longBranch_sublist hw hs hv forward hori
  · simpa only [shortBranch_eq_interiors hw hs forward] using shortBranch_sublist hw hs hv forward hori

theorem sublist_range_before {q : Queue} {f : Nat → Nat} {m i j : Nat}
    (hq : q.Nodup) (hsub : ((List.range m).map f).Sublist q)
    (hi : i < m) (hj : j < m) (hij : i < j) : q.idxOf (f i) < q.idxOf (f j) := by
  have hp : q.Pairwise (fun a b => q.idxOf a < q.idxOf b) := by
    apply List.pairwise_iff_getElem.mpr
    intro a b ha hb hab
    simpa only [hq.idxOf_getElem a ha, hq.idxOf_getElem b hb] using hab
  have h := List.pairwise_iff_getElem.mp (hp.sublist hsub) i j
    (by simpa) (by simpa) hij
  simpa using h

theorem folded_directed_edge {w a b : Nat} (hw : 2 ≤ w)
    (ha : a < 2 * w + 1) (hb : b < 2 * w + 1)
    (hab : cycleAdjacent (2 * w + 1) a b = true)
    (horder : foldedIndex w a < foldedIndex w b) :
    (∃ k, k ≤ w ∧ a = k ∧ b = k + 1) ∨
      (∃ k, k < w ∧ a = reflect (2 * w + 1) k ∧
        b = reflect (2 * w + 1) (k + 1)) := by
  rcases (cycleAdjacent_iff ha hb).mp hab with h | h | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · left
    refine ⟨a, ?_, rfl, h.symm⟩
    unfold foldedIndex at horder
    split_ifs at horder <;> omega
  · right
    have hbig : w + 1 < a := by
      unfold foldedIndex at horder
      split_ifs at horder <;> omega
    refine ⟨2 * w + 1 - a, by omega, ?_, ?_⟩
    · rw [reflect_eq (by omega), if_neg (by omega)]
      omega
    · rw [reflect_eq (by omega), if_neg (by omega)]
      omega
  · right
    refine ⟨0, by omega, ?_, ?_⟩
    · simp [reflect]
    · rw [reflect_eq (by omega), if_neg (by omega)]
      omega
  · simp only [foldedIndex, Nat.zero_le, if_true] at horder
    omega

theorem orientation_eq_of_branches {w source : Nat} {s : State}
    (hw : 2 ≤ w) (hs : source < 2 * w + 1) (hv : Valid (2 * w + 1) s) (forward : Bool)
    (hlong : (longBranch w source forward).Sublist (placement s))
    (hshort : (shortBranch w source forward).Sublist (placement s)) :
    orientation (2 * w + 1) s = orientation (2 * w + 1) (branchState w source forward) := by
  have hn : 0 < 2 * w + 1 := by omega
  have hforward (a b : Nat) (ha : a < 2 * w + 1) (hb : b < 2 * w + 1)
      (hadj : cycleAdjacent (2 * w + 1) a b = true)
      (hbefore : (branchWord w source forward).idxOf a < (branchWord w source forward).idxOf b) :
      (placement s).idxOf a < (placement s).idxOf b := by
    have hca := cycleCoord_lt hn forward (k := a) (source := source)
    have hcb := cycleCoord_lt hn forward (k := b) (source := source)
    rw [branchWord_idxOf hw hs ha forward, branchWord_idxOf hw hs hb forward] at hbefore
    have he := folded_directed_edge hw hca hcb ((cycleCoord_adj_iff hs ha hb forward).mpr hadj) hbefore
    have hea := cycleLabel_coord hs ha forward
    have heb := cycleLabel_coord hs hb forward
    rcases he with ⟨k, hk, hka, hkb⟩ | ⟨k, hk, hka, hkb⟩
    · rw [hka] at hea
      rw [hkb] at heb
      rw [← hea, ← heb]
      exact sublist_range_before hv.placement_nodup hlong (by omega) (by omega) (by omega)
    · rw [hka, ← cycleLabel_not (by omega) forward] at hea
      rw [hkb, ← cycleLabel_not (by omega) forward] at heb
      rw [← hea, ← heb]
      exact sublist_range_before hv.placement_nodup hshort (by omega) (by omega) (by omega)
  apply List.map_congr_left
  intro a ha
  have ha' := List.mem_range.mp ha
  have hb : (a + 1) % (2 * w + 1) < 2 * w + 1 := Nat.mod_lt _ hn
  have hadj : cycleAdjacent (2 * w + 1) a ((a + 1) % (2 * w + 1)) = true := by
    simp [cycleAdjacent]
  have hne : a ≠ (a + 1) % (2 * w + 1) := by
    intro he
    have := (cycleAdjacent_iff ha' hb).mp hadj
    rcases this with h | h | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
  have hind := (List.idxOf_inj ((branchState_valid hw hs forward).placement_mem.mpr ha')).not.mpr hne
  simp only [placement, branchState, List.reverse_nil, List.append_nil] at hind
  apply decide_eq_decide.mpr
  simp only [placement, branchState, List.reverse_nil, List.append_nil]
  constructor
  · intro h
    by_contra hc
    have hr := hforward _ _ hb ha' (by simpa only [cycleAdjacent_symm] using hadj) (by omega)
    exact Nat.lt_asymm h hr
  · exact hforward _ _ ha' hb hadj

theorem orientation_of_placement_interleaving {w source : Nat} {s : State}
    (hw : 2 ≤ w) (hs : source < 2 * w + 1) (hv : Valid (2 * w + 1) s) (forward : Bool)
    {mid : Queue} (hm : mid ∈ interleavings (longInterior w source forward) (shortInterior w source forward))
    (heq : placement s = source :: mid ++ [cycleLabel (2 * w + 1) source forward (w + 1)]) :
    orientation (2 * w + 1) s = orientation (2 * w + 1) (branchState w source forward) := by
  have hc := (branchState_valid hw hs forward).placement_nodup
  simp only [placement, branchState, List.reverse_nil, List.append_nil, branchWord_eq_interiors] at hc
  have hn := (List.nodup_append.mp (List.nodup_cons.mp hc).2).1
  obtain ⟨_, hl, hr⟩ := (mem_interleavings_iff hn).mp hm
  apply orientation_eq_of_branches hw hs hv forward
  · rw [longBranch_eq_interiors hs forward, heq]
    exact (List.Sublist.cons₂ source hl).append (List.Sublist.refl _)
  · rw [shortBranch_eq_interiors hw hs forward, heq]
    exact (List.Sublist.cons₂ source hr).append (List.Sublist.refl _)

theorem longInterior_eq_range' (w source : Nat) (forward : Bool) :
    longInterior w source forward = (List.range' 1 w).map (cycleLabel (2 * w + 1) source forward) := by
  simp [longInterior, List.range'_eq_map_range, List.map_map, Function.comp_def, Nat.add_comm]

theorem shortInterior_eq_range' {w source : Nat} (hw : 2 ≤ w) (forward : Bool) :
    shortInterior w source forward = (List.range' 1 (w - 1)).map (cycleLabel (2 * w + 1) source (!forward)) := by
  simp only [shortInterior, List.range'_eq_map_range, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  simp only [Function.comp_apply]
  rw [cycleLabel_not (by omega) forward, reflect_eq (by omega), if_neg (by omega)]
  congr 2
  omega

theorem interleaving_first_branch {w source : Nat} (hw : 2 ≤ w) (forward : Bool) {mid : Queue}
    (hm : mid ∈ interleavings (longInterior w source forward) (shortInterior w source forward)) :
    (∃ rest, mid = cycleLabel (2 * w + 1) source forward 1 :: rest ∧
      rest ∈ interleavings ((List.range' 2 (w - 1)).map (cycleLabel (2 * w + 1) source forward))
        (shortInterior w source forward)) ∨
    (∃ rest, mid = cycleLabel (2 * w + 1) source (!forward) 1 :: rest ∧
      rest ∈ interleavings ((List.range' 2 (w - 2)).map (cycleLabel (2 * w + 1) source (!forward)))
        (longInterior w source forward)) := by
  have hrange (k : Nat) (hk : 1 ≤ k) : List.range' 1 k = 1 :: List.range' 2 (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, List.range'_succ]
  have hl : longInterior w source forward = cycleLabel (2 * w + 1) source forward 1 ::
      (List.range' 2 (w - 1)).map (cycleLabel (2 * w + 1) source forward) := by
    rw [longInterior_eq_range', hrange w (by omega), List.map_cons]
  have hs : shortInterior w source forward = cycleLabel (2 * w + 1) source (!forward) 1 ::
      (List.range' 2 (w - 2)).map (cycleLabel (2 * w + 1) source (!forward)) := by
    rw [shortInterior_eq_range' hw, hrange (w - 1) (by omega), List.map_cons]
    congr 3
  rw [hl, hs, interleavings, List.mem_append, List.mem_map, List.mem_map] at hm
  rcases hm with ⟨rest, hr, rfl⟩ | ⟨rest, hr, rfl⟩
  · exact Or.inl ⟨rest, rfl, by simpa only [hs] using hr⟩
  · exact Or.inr ⟨rest, rfl, (interleavings_swap _ _).mem_iff.mp (by simpa only [hl] using hr)⟩

end OddCycle
