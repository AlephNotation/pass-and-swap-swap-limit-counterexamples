import OddCycle.CircularBlockMoves
import OddCycle.CycleArcBlocks
import OddCycle.CycleSymmetry

/-! Translating a single cycle-edge reversal to a complemented orientation
bit, including changes of the circular index origin. -/

namespace OddCycle

theorem clockwise_not_reverse {n a b : Nat} (hn : 3 ≤ n) (ha : a < n) (hb : b < n)
    (h : Clockwise n a b) : ¬ Clockwise n b a := by
  intro hh
  have h1 := (clockwise_iff ha).mp h
  have h2 := (clockwise_iff hb).mp hh
  omega

theorem cycle_edge_index_unique {n i j : Nat} (hn : 3 ≤ n) (hi : i < n) (hj : j < n)
    (h : (j = i ∧ (j + 1) % n = (i + 1) % n) ∨
      (j = (i + 1) % n ∧ (j + 1) % n = i)) : j = i := by
  rcases h with h | ⟨rfl, h⟩
  · exact h.1
  · exact False.elim (clockwise_not_reverse hn hi hj rfl h)

theorem edgeBits_eq_of_erase {n i : Nat} {s t : State} (hn : 3 ≤ n) (hi : i < n)
    (he : EdgeEquiv (eraseEdge (cycleAdjacent n) i ((i + 1) % n)) (placement s) (placement t)) :
    ∀ j < n, j ≠ i → edgeBit n s j = edgeBit n t j := by
  intro j hj hji
  have hnedge : ¬ ((j = i ∧ (j + 1) % n = (i + 1) % n) ∨
      (j = (i + 1) % n ∧ (j + 1) % n = i)) := fun h => hji (cycle_edge_index_unique hn hi hj h)
  have ha : eraseEdge (cycleAdjacent n) i ((i + 1) % n) j ((j + 1) % n) = true := by
    simp [eraseEdge, cycleAdjacent]
    tauto
  simp only [edgeBit, he.before_iff ha]

theorem edgeEquiv_erase_of_bits {n i : Nat} {s t : State} (hn : 3 ≤ n)
    (hs : Valid n s) (ht : Valid n t)
    (hbits : ∀ j < n, j ≠ i → edgeBit n s j = edgeBit n t j) :
    EdgeEquiv (eraseEdge (cycleAdjacent n) i ((i + 1) % n)) (placement s) (placement t) := by
  apply WordReachable.edgeEquiv (eraseEdge_symm (cycleAdjacent_symm n) _ _)
  apply word_reachable_of_before (eraseEdge_symm (cycleAdjacent_symm n) _ _) hs.placement_nodup
    (hs.placement_perm.trans ht.placement_perm.symm)
  intro a ha b hb hab
  have hal := hs.placement_mem.mp ha
  have hbl := hs.placement_mem.mp hb
  have hedge : cycleAdjacent n a b = true ∧
      ¬ ((a = i ∧ b = (i + 1) % n) ∨ (a = (i + 1) % n ∧ b = i)) := by
    simp [eraseEdge] at hab
    exact ⟨hab.1, by tauto⟩
  rcases (cycleAdjacent_clockwise_iff n a b).mp hedge.1 with hab' | hba'
  · change (a + 1) % n = b at hab'
    have hai : a ≠ i := by
      intro he
      apply hedge.2
      exact Or.inl ⟨he, by simpa only [← he] using hab'.symm⟩
    have he := hbits a hal hai
    have hh : (edgeBit n s a = true) ↔ (edgeBit n t a = true) := by rw [he]
    simpa only [edgeBit, hab', decide_eq_true_eq] using hh
  · change (b + 1) % n = a at hba'
    have hbi : b ≠ i := by
      intro he
      apply hedge.2
      exact Or.inr ⟨by simpa only [← he] using hba'.symm, he⟩
    have he := hbits b hbl hbi
    have hh : (edgeBit n s b = false) ↔ (edgeBit n t b = false) := by rw [he]
    simpa only [edgeBit_false_iff (by omega) hbl hs, edgeBit_false_iff (by omega) hbl ht, hba'] using hh

def EdgeBitFlip (n : Nat) (s t : State) (i : Nat) : Prop :=
  (∀ j < n, j ≠ i → edgeBit n s j = edgeBit n t j) ∧ edgeBit n t i = !(edgeBit n s i)

theorem mod_add_injective {n a b : Nat} (k : Nat) (ha : a < n) (hb : b < n)
    (he : (k + a) % n = (k + b) % n) : a = b := by
  apply eq_of_zmod_eq ha hb
  have hh := congrArg (fun x : Nat => (x : ZMod n)) he
  simp only [ZMod.natCast_mod, Nat.cast_add] at hh
  exact add_left_cancel hh

theorem mod_add_surjective {n v : Nat} (k : Nat) (hv : v < n) :
    ∃ a, a < n ∧ (k + a) % n = v := by
  have hn : 0 < n := by omega
  refine ⟨unrotate n (k % n) v, Nat.mod_lt _ hn, ?_⟩
  have hh := rotate_unrotate (Nat.mod_lt k hn) hv
  simpa only [rotate, Nat.mod_add_mod] using hh

theorem rotatedFlipAt_iff_edgeBitFlip {n i : Nat} {s t : State} (k : Nat) (hi : i < n) :
    CircularWord.FlipAt ((orientation n s).rotate k) ((orientation n t).rotate k) i ↔
      EdgeBitFlip n s t ((k + i) % n) := by
  constructor
  · intro h
    constructor
    · intro j hj hji
      obtain ⟨a, ha, haj⟩ := mod_add_surjective k hj
      have hai : a ≠ i := by intro he; subst a; exact hji haj.symm
      have hh := h.getElem a (by simpa only [List.length_rotate, orientation_length] using ha)
      simpa only [orientation_rotate_getElem s k ha, orientation_rotate_getElem t k ha,
        if_neg hai, haj] using hh.symm
    · have hh := h.getElem i (by simpa only [List.length_rotate, orientation_length] using hi)
      simpa only [orientation_rotate_getElem s k hi, orientation_rotate_getElem t k hi, if_pos rfl] using hh
  · intro h
    apply CircularWord.flipAt_of_getElem (by simp only [List.length_rotate, orientation_length])
      (by simpa only [List.length_rotate, orientation_length] using hi)
    intro a ha
    have han : a < n := by simpa only [List.length_rotate, orientation_length] using ha
    simp only [orientation_rotate_getElem s k han, orientation_rotate_getElem t k han]
    by_cases he : a = i
    · subst a
      simpa only [if_pos rfl] using h.2
    · have hne : (k + a) % n ≠ (k + i) % n := fun hh => he (mod_add_injective k han hi hh)
      simpa only [if_neg he] using (h.1 _ (Nat.mod_lt _ (by omega)) hne).symm

theorem edgeBitFlip_of_erase_of_ne {n i : Nat} {s t : State} (hn : 3 ≤ n) (hi : i < n)
    (he : EdgeEquiv (eraseEdge (cycleAdjacent n) i ((i + 1) % n)) (placement s) (placement t))
    (hne : orientation n s ≠ orientation n t) : EdgeBitFlip n s t i := by
  have hrest := edgeBits_eq_of_erase hn hi he
  refine ⟨hrest, ?_⟩
  have hh : edgeBit n s i ≠ edgeBit n t i := by
    intro hsame
    apply hne
    apply List.ext_getElem
    · simp only [orientation_length]
    · intro j hj hjt
      have hjn : j < n := by simpa only [orientation_length] using hj
      simp only [orientation_getElem hjn]
      by_cases hji : j = i
      · simpa only [hji] using hsame
      · exact hrest j hjn hji
  cases hsbit : edgeBit n s i <;> cases htbit : edgeBit n t i <;> simp only [hsbit, htbit] at hh ⊢ <;> simp_all only [Bool.not_false, Bool.not_true]

theorem EdgeBitFlip.orientation_ne {n i : Nat} {s t : State} (hi : i < n)
    (h : EdgeBitFlip n s t i) : orientation n s ≠ orientation n t := by
  intro he
  have hh : (orientation n s)[i]'(by simpa only [orientation_length] using hi) =
      (orientation n t)[i]'(by simpa only [orientation_length] using hi) := by simp only [he]
  simp only [orientation_getElem hi] at hh
  have hn := h.2
  rw [hh] at hn
  cases edgeBit n t i <;> simp at hn

end OddCycle
