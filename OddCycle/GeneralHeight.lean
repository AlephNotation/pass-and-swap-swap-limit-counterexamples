import OddCycle.BalancedGeometry
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists

/-! Directed-path height for every balanced odd-cycle orientation. -/

namespace OddCycle

theorem pathEdges_iff_isChain (adj : Nat → Nat → Bool) (q : Queue) :
    pathEdges adj q = true ↔ q.IsChain (fun a b => adj a b = true) := by
  induction q with
  | nil => simp [pathEdges]
  | cons a q ih =>
    cases q with
    | nil => simp [pathEdges]
    | cons b q => simpa [pathEdges] using and_congr Iff.rfl ih

theorem path_rank_length_le {adj : Nat → Nat → Bool} {rank : Nat → Nat} {bound : Nat}
    (a : Nat) (q : Queue) (ho : RankOrdered adj rank (a :: q))
    (hp : pathEdges adj (a :: q) = true) (hb : ∀ x ∈ a :: q, rank x ≤ bound) :
    rank a + q.length ≤ bound := by
  induction q generalizing a with
  | nil => simpa using hb a (by simp)
  | cons b q ih =>
    have he : adj a b = true ∧ pathEdges adj (b :: q) = true := by
      simpa only [pathEdges, Bool.and_eq_true] using hp
    have hpair := List.pairwise_cons.mp ho
    have hab := hpair.1 b (by simp) he.1
    have hh := ih b hpair.2 he.2 (fun x hx => hb x (by simp [hx]))
    simp only [List.length_cons]
    omega

theorem foldl_max_le {q : List Nat} {initial bound : Nat}
    (hi : initial ≤ bound) (hq : ∀ x ∈ q, x ≤ bound) : q.foldl max initial ≤ bound := by
  induction q generalizing initial with
  | nil => exact hi
  | cons x q ih =>
    exact ih (max_le hi (hq x (by simp))) (fun y hy => hq y (by simp [hy]))

theorem le_foldl_max_of_mem {q : List Nat} {x initial : Nat} (hx : x ∈ q) :
    x ≤ q.foldl max initial := by
  have hinit (r : List Nat) (a : Nat) : a ≤ r.foldl max a := by
    induction r generalizing a with
    | nil => exact Nat.le_refl _
    | cons b r ih => exact (le_max_left a b).trans (ih (max a b))
  induction q generalizing initial with
  | nil => simp at hx
  | cons y q ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (le_max_right initial x).trans (hinit q (max initial x))
    · exact ih hx

theorem height_le_of_rank {n bound : Nat} {s : State} {rank : Nat → Nat}
    (ho : RankOrdered (cycleAdjacent n) rank (placement s))
    (hb : ∀ x ∈ placement s, rank x ≤ bound) : height n s ≤ bound := by
  apply foldl_max_le (Nat.zero_le _)
  intro k hk
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  obtain ⟨hp, he⟩ := List.mem_filter.mp hp
  have hsub := List.mem_sublists.mp hp
  cases p with
  | nil => simp
  | cons a q =>
    have hh := path_rank_length_le a q (ho.sublist hsub) he
      (fun x hx => hb x (hsub.subset hx))
    simp only [List.length_cons, Nat.add_sub_cancel]
    omega

theorem path_length_le_height {n : Nat} {s : State} {p : Queue}
    (hp : p.Sublist (placement s)) (he : pathEdges (cycleAdjacent n) p = true) :
    p.length - 1 ≤ height n s := by
  apply le_foldl_max_of_mem
  exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨List.mem_sublists.mpr hp, he⟩, rfl⟩

/-- An increasing sequence of positions is a subsequence of the placement. -/
theorem sublist_of_idxOf_pairwise {p q : Queue} (hq : q.Nodup)
    (hm : ∀ x ∈ p, x ∈ q)
    (ho : p.Pairwise (fun a b => q.idxOf a < q.idxOf b)) : p.Sublist q := by
  let r := fun a b => q.idxOf a < q.idxOf b
  letI : Std.Antisymm r := ⟨fun _ _ hab hba => False.elim (Nat.lt_asymm hab hba)⟩
  have hp : p.Nodup := ho.imp (fun {a b} hab heq => by subst b; exact Nat.lt_irrefl _ hab)
  apply List.sublist_of_subperm_of_pairwise (r := r) (List.subperm_of_subset hp hm) ho
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simpa only [r, hq.idxOf_getElem i hi, hq.idxOf_getElem j hj] using hij

def longBranch (w source : Nat) (forward : Bool) : Queue :=
  (List.range (w + 2)).map (cycleLabel (2 * w + 1) source forward)

theorem longBranch_path {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (forward : Bool) :
    pathEdges (cycleAdjacent (2 * w + 1)) (longBranch w source forward) = true := by
  rw [pathEdges_iff_isChain, longBranch, List.isChain_map, List.isChain_range_succ]
  intro k hk
  apply (cycleLabel_adj_iff hs (by omega) (by omega) forward).mpr
  simp [cycleAdjacent, Nat.mod_eq_of_lt (show k + 1 < 2 * w + 1 by omega)]

theorem longBranch_sublist {w source : Nat} {s : State} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (hv : Valid (2 * w + 1) s) (forward : Bool)
    (hori : orientation (2 * w + 1) s = orientation (2 * w + 1) (branchState w source forward)) :
    (longBranch w source forward).Sublist (placement s) := by
  have hn : 0 < 2 * w + 1 := by omega
  apply sublist_of_idxOf_pairwise hv.placement_nodup
  · intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    exact hv.placement_mem.mpr (cycleLabel_lt hn forward)
  · letI : Trans (fun a b => (placement s).idxOf a < (placement s).idxOf b)
        (fun a b => (placement s).idxOf a < (placement s).idxOf b)
        (fun a b => (placement s).idxOf a < (placement s).idxOf b) := ⟨Nat.lt_trans⟩
    apply List.IsChain.pairwise
    rw [longBranch, List.isChain_map, List.isChain_range_succ]
    intro k hk
    have ha : k < 2 * w + 1 := by omega
    have hb : k + 1 < 2 * w + 1 := by omega
    have hadj : cycleAdjacent (2 * w + 1) k (k + 1) = true := by
      simp [cycleAdjacent, Nat.mod_eq_of_lt hb]
    apply (orientation_before_iff hv (branchState_valid hw hs forward) hori
      (cycleLabel_lt hn forward) (cycleLabel_lt hn forward)
      ((cycleLabel_adj_iff hs ha hb forward).mpr hadj)).mpr
    simp only [placement, branchState, List.reverse_nil, List.append_nil]
    rw [branchWord_idxOf_label hw hs ha forward, branchWord_idxOf_label hw hs hb forward]
    unfold foldedIndex
    split_ifs <;> omega

theorem balanced_height {w : Nat} (hw : 2 ≤ w) {s : State}
    (hv : Valid (2 * w + 1) s) (hb : balanced w s = true) : height (2 * w + 1) s = w + 1 := by
  simp only [balanced, List.any_eq_true, beq_iff_eq] at hb
  obtain ⟨source, hsource, forward, _, hori⟩ := hb
  have hs := List.mem_range.mp hsource
  apply Nat.le_antisymm
  · apply height_le_of_rank (rankOrdered_of_orientation hw hs hv forward hori)
    intro x _
    exact branchRank_bound (cycleCoord_lt (by omega) forward)
  · have hh := path_length_le_height (longBranch_sublist hw hs hv forward hori)
      (longBranch_path hw hs forward)
    simpa [longBranch] using hh

end OddCycle
