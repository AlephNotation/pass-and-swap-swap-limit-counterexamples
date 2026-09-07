import OddCycle.Model
import OddCycle.CycleCoordinates
import Mathlib.Data.List.Nodup

namespace OddCycle

/-- Coordinates of the canonical linear extension: ascend the long branch's
interior, then descend the other side of the cycle to the common sink. -/
def foldedWord (w : Nat) : Queue :=
  List.range (w + 1) ++ (List.range' (w + 1) w).reverse

def foldedIndex (w k : Nat) : Nat := if k ≤ w then k else 3 * w + 1 - k

theorem foldedIndex_lt {w k : Nat} (hk : k < 2 * w + 1) :
    foldedIndex w k < 2 * w + 1 := by
  unfold foldedIndex
  split <;> omega

theorem foldedIndex_involutive {w k : Nat} (hk : k < 2 * w + 1) :
    foldedIndex w (foldedIndex w k) = k := by
  unfold foldedIndex
  split_ifs <;> omega

theorem foldedIndex_injective {w a b : Nat} (ha : a < 2 * w + 1)
    (hb : b < 2 * w + 1) (h : foldedIndex w a = foldedIndex w b) : a = b := by
  have hh := congrArg (foldedIndex w) h
  simpa [foldedIndex_involutive ha, foldedIndex_involutive hb] using hh

theorem foldedWord_eq_map (w : Nat) :
    foldedWord w = (List.range (2 * w + 1)).map (foldedIndex w) := by
  rw [show 2 * w + 1 = (w + 1) + w by omega, List.range_add, List.map_append, List.map_map]
  unfold foldedWord
  congr 1
  · symm
    calc
      _ = (List.range (w + 1)).map (fun k => k) := by
        apply List.map_congr_left
        intro k hk
        simp only [List.mem_range] at hk
        simp [foldedIndex, show k ≤ w by omega]
      _ = _ := List.map_id' _
  · rw [List.reverse_range']
    apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    simp only [Function.comp_apply, foldedIndex]
    split_ifs <;> omega

theorem idxOf_map_of_injOn (f : Nat → Nat) (n a : Nat) (q : Queue)
    (hinj : ∀ x y, x < n → y < n → f x = f y → x = y)
    (ha : a < n) (hq : ∀ x ∈ q, x < n) :
    (q.map f).idxOf (f a) = q.idxOf a := by
  induction q with
  | nil => rfl
  | cons x xs ih =>
    have hx := hq x (by simp)
    have ht := ih (fun y hy => hq y (by simp [hy]))
    by_cases hxa : x = a
    · subst x; simp
    · have hf : f x ≠ f a := fun h => hxa (hinj x a hx ha h)
      simp [hxa, hf, ht]

theorem foldedWord_idxOf {w k : Nat} (hk : k < 2 * w + 1) :
    (foldedWord w).idxOf k = foldedIndex w k := by
  rw [foldedWord_eq_map]
  conv_lhs => rw [← foldedIndex_involutive hk]
  rw [idxOf_map_of_injOn (foldedIndex w) (2 * w + 1) (foldedIndex w k)
    (List.range (2 * w + 1))
    (fun _ _ => foldedIndex_injective) (foldedIndex_lt hk) (by simp)]
  have hh := (List.nodup_range (n := 2 * w + 1)).idxOf_getElem
    (foldedIndex w k) (by simpa using foldedIndex_lt hk)
  simpa using hh

def cycleLabel (n source : Nat) (forward : Bool) (k : Nat) : Nat :=
  (source + if forward then k else n - k) % n

def cycleCoord (n source : Nat) (forward : Bool) (k : Nat) : Nat :=
  if forward then unrotate n source k else reflect n (unrotate n source k)

theorem cycleLabel_eq_rotate (n source k : Nat) (forward : Bool) :
    cycleLabel n source forward k = rotate n source (if forward then k else reflect n k) := by
  cases forward <;> simp [cycleLabel, rotate, reflect, Nat.add_mod_mod]

theorem cycleLabel_lt {n source k : Nat} (hn : 0 < n) (forward : Bool) :
    cycleLabel n source forward k < n := Nat.mod_lt _ hn

theorem cycleCoord_lt {n source k : Nat} (hn : 0 < n) (forward : Bool) :
    cycleCoord n source forward k < n := by
  cases forward <;> exact Nat.mod_lt _ hn

theorem cycleCoord_label {n source k : Nat} (hs : source < n) (hk : k < n) (forward : Bool) :
    cycleCoord n source forward (cycleLabel n source forward k) = k := by
  have hn : 0 < n := by omega
  rw [cycleLabel_eq_rotate]
  cases forward
  · change reflect n (unrotate n source (rotate n source (reflect n k))) = k
    rw [unrotate_rotate (k := reflect n k) hs (Nat.mod_lt _ hn), reflect_involutive hk]
  · exact unrotate_rotate hs hk

theorem cycleLabel_coord {n source k : Nat} (hs : source < n) (hk : k < n) (forward : Bool) :
    cycleLabel n source forward (cycleCoord n source forward k) = k := by
  have hn : 0 < n := by omega
  rw [cycleLabel_eq_rotate]
  cases forward
  · change rotate n source (reflect n (reflect n (unrotate n source k))) = k
    rw [reflect_involutive (k := unrotate n source k) (Nat.mod_lt _ hn), rotate_unrotate hs hk]
  · exact rotate_unrotate hs hk

theorem cycleLabel_injective {n source a b : Nat} (hs : source < n)
    (ha : a < n) (hb : b < n) (forward : Bool)
    (h : cycleLabel n source forward a = cycleLabel n source forward b) : a = b := by
  have hh := congrArg (cycleCoord n source forward) h
  simpa [cycleCoord_label hs ha forward, cycleCoord_label hs hb forward] using hh

theorem cycleLabel_adj_iff {n source a b : Nat} (hs : source < n)
    (ha : a < n) (hb : b < n) (forward : Bool) :
    cycleAdjacent n (cycleLabel n source forward a) (cycleLabel n source forward b) = true ↔
      cycleAdjacent n a b = true := by
  have hn : 0 < n := by omega
  rw [cycleLabel_eq_rotate, cycleLabel_eq_rotate]
  cases forward
  · exact (rotate_adj_iff hs (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)).trans (reflect_adj_iff ha hb)
  · exact rotate_adj_iff hs ha hb

theorem cycleCoord_adj_iff {n source a b : Nat} (hs : source < n)
    (ha : a < n) (hb : b < n) (forward : Bool) :
    cycleAdjacent n (cycleCoord n source forward a) (cycleCoord n source forward b) = true ↔
      cycleAdjacent n a b = true := by
  have hn : 0 < n := by omega
  have h := cycleLabel_adj_iff (a := cycleCoord n source forward a)
    (b := cycleCoord n source forward b) hs (cycleCoord_lt hn forward) (cycleCoord_lt hn forward) forward
  simpa only [cycleLabel_coord hs ha forward, cycleLabel_coord hs hb forward] using h.symm

theorem cycleCoord_eq_iff {n source x k : Nat} (hs : source < n)
    (hx : x < n) (hk : k < n) (forward : Bool) :
    cycleCoord n source forward x = k ↔ x = cycleLabel n source forward k := by
  constructor
  · intro h
    rw [← h, cycleLabel_coord hs hx forward]
  · rintro rfl
    exact cycleCoord_label hs hk forward

theorem branchWord_eq_map_folded {w source : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (forward : Bool) :
    branchWord w source forward = (foldedWord w).map (cycleLabel (2 * w + 1) source forward) := by
  have hcut : List.range' (w + 1) w = (w + 1) :: List.range' (w + 2) (w - 1) := by
    calc
      _ = List.range' (w + 1) ((w - 1) + 1) := by
        congr 1; omega
      _ = _ := by rw [List.range'_succ]
  have htail : (List.range' (w + 1) w).reverse =
      (List.range (w - 1)).map (fun j => 2 * w + 1 - (j + 1)) ++ [w + 1] := by
    rw [hcut, List.reverse_cons, List.reverse_range']
    congr 1
    apply List.map_congr_left
    intro j _
    omega
  unfold foldedWord
  rw [List.map_append, List.range_succ_eq_map, htail]
  cases forward <;>
    simp [branchWord, cycleLabel, List.map_map, Function.comp_def,
      List.append_assoc, Nat.mod_eq_of_lt hs]

theorem foldedWord_mem_iff {w k : Nat} : k ∈ foldedWord w ↔ k < 2 * w + 1 := by
  rw [foldedWord_eq_map, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact foldedIndex_lt (List.mem_range.mp ha)
  · intro hk
    exact ⟨foldedIndex w k, List.mem_range.mpr (foldedIndex_lt hk), foldedIndex_involutive hk⟩

theorem foldedWord_nodup (w : Nat) : (foldedWord w).Nodup := by
  rw [foldedWord_eq_map]
  apply List.Nodup.map_on _ List.nodup_range
  intro a ha b hb hab
  exact foldedIndex_injective (List.mem_range.mp ha) (List.mem_range.mp hb) hab

theorem branchWord_idxOf_label {w source k : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (hk : k < 2 * w + 1) (forward : Bool) :
    (branchWord w source forward).idxOf (cycleLabel (2 * w + 1) source forward k) =
      foldedIndex w k := by
  rw [branchWord_eq_map_folded hw hs forward]
  rw [idxOf_map_of_injOn _ (2 * w + 1) k _
    (fun _ _ ha hb h => cycleLabel_injective hs ha hb forward h) hk
    (fun _ hx => foldedWord_mem_iff.mp hx)]
  exact foldedWord_idxOf hk

theorem branchWord_idxOf {w source k : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (hk : k < 2 * w + 1) (forward : Bool) :
    (branchWord w source forward).idxOf k =
      foldedIndex w (cycleCoord (2 * w + 1) source forward k) := by
  conv_lhs => rw [← cycleLabel_coord hs hk forward]
  exact branchWord_idxOf_label hw hs (cycleCoord_lt (by omega) forward) forward

/-- Distance along each branch, with the short branch's last edge increasing
the rank by two. Thus rank w occurs at just the long branch's penultimate job. -/
def branchRank (w k : Nat) : Nat := if k ≤ w + 1 then k else 2 * w + 1 - k

theorem branchRank_bound {w k : Nat} (hk : k < 2 * w + 1) : branchRank w k ≤ w + 1 := by
  unfold branchRank
  split <;> omega

theorem branchRank_boundary {w a b : Nat}
    (ha : a < 2 * w + 1) (hb : b < 2 * w + 1)
    (hhigh : w ≤ branchRank w a) (hup : branchRank w a < branchRank w b) :
    a = w ∧ b = w + 1 := by
  unfold branchRank at *
  split_ifs at * <;> omega

theorem foldedIndex_lt_iff_rank {w a b : Nat} (hw : 2 ≤ w)
    (ha : a < 2 * w + 1) (hb : b < 2 * w + 1)
    (hab : cycleAdjacent (2 * w + 1) a b = true) :
    foldedIndex w a < foldedIndex w b ↔ branchRank w a < branchRank w b := by
  have he := (cycleAdjacent_iff ha hb).mp hab
  unfold foldedIndex branchRank
  split_ifs <;> omega

theorem reflect_eq {n k : Nat} (hk : k < n) :
    reflect n k = if k = 0 then 0 else n - k := by
  by_cases hz : k = 0
  · simp [reflect, hz]
  · simp [reflect, hz, Nat.mod_eq_of_lt (show n - k < n by omega)]

theorem foldedIndex_flip_iff {w a b : Nat} (hw : 2 ≤ w)
    (ha : a < 2 * w + 1) (hb : b < 2 * w + 1)
    (hab : cycleAdjacent (2 * w + 1) a b = true)
    (hex : ¬ ((a = w ∧ b = w + 1) ∨ (a = w + 1 ∧ b = w))) :
    foldedIndex w a < foldedIndex w b ↔
      foldedIndex w (reflect (2 * w + 1) a) < foldedIndex w (reflect (2 * w + 1) b) := by
  have he := (cycleAdjacent_iff ha hb).mp hab
  rw [reflect_eq ha, reflect_eq hb]
  unfold foldedIndex
  split_ifs <;> omega

theorem cycleCoord_not {n source k : Nat} (hn : 0 < n) (forward : Bool) :
    cycleCoord n source (!forward) k = reflect n (cycleCoord n source forward k) := by
  cases forward
  · exact (reflect_involutive (k := unrotate n source k) (Nat.mod_lt _ hn)).symm
  · rfl

end OddCycle
