import OddCycle.CycleGeometry
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! Cyclic coordinates form a group. We use ZMod for the dihedral coordinate
identities, keeping the operational model's natural-number labels unchanged. -/

namespace OddCycle

theorem eq_of_zmod_eq {n a b : Nat} (ha : a < n) (hb : b < n)
    (h : (a : ZMod n) = (b : ZMod n)) : a = b := by
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using congrArg ZMod.val h

theorem cast_rotate (n source k : Nat) :
    (rotate n source k : ZMod n) = (source : ZMod n) + k := by
  simp [rotate, ZMod.natCast_mod]

theorem cast_reflect {n k : Nat} (hk : k < n) :
    (reflect n k : ZMod n) = -(k : ZMod n) := by
  simp [reflect, ZMod.natCast_mod, Nat.cast_sub hk.le]

theorem cast_unrotate {n source : Nat} (hs : source < n) (k : Nat) :
    (unrotate n source k : ZMod n) = -(source : ZMod n) + k := by
  simp [unrotate, ZMod.natCast_mod, Nat.cast_sub hs.le]

theorem cast_cycleLabel {n source k : Nat} (hk : k < n) (forward : Bool) :
    (cycleLabel n source forward k : ZMod n) =
      (source : ZMod n) + if forward then (k : ZMod n) else -(k : ZMod n) := by
  cases forward <;>
    simp [cycleLabel, ZMod.natCast_mod, Nat.cast_sub hk.le]

theorem cast_cycleCoord {n source : Nat} (hs : source < n) (forward : Bool) (k : Nat) :
    (cycleCoord n source forward k : ZMod n) =
      if forward then -(source : ZMod n) + k else (source : ZMod n) - k := by
  have hn : 0 < n := by omega
  cases forward
  · change (reflect n (unrotate n source k) : ZMod n) = _
    rw [cast_reflect (k := unrotate n source k) (Nat.mod_lt _ hn), cast_unrotate hs k]
    simp [sub_eq_add_neg, add_comm]
  · exact cast_unrotate hs k

theorem cycleCoord_rebase {n source m k : Nat}
    (hm : m < n) (hk : k < n) (forward : Bool) :
    cycleCoord n (cycleLabel n source forward m) (!forward) (cycleLabel n source forward k) =
      rotate n m (reflect n k) := by
  have hn : 0 < n := by omega
  apply eq_of_zmod_eq (cycleCoord_lt hn (!forward))
    (show rotate n m (reflect n k) < n from Nat.mod_lt _ hn)
  rw [cast_cycleCoord (cycleLabel_lt hn forward), cast_rotate, cast_reflect hk,
    cast_cycleLabel hm forward, cast_cycleLabel hk forward]
  cases forward <;> simp <;> ring

def reverseCoord (w k : Nat) : Nat := rotate (2 * w + 1) (w + 1) (reflect (2 * w + 1) k)

theorem cycleCoord_reverse_frame {w source x : Nat} (hw : 2 ≤ w)
    (hs : source < 2 * w + 1) (hx : x < 2 * w + 1) (forward : Bool) :
    cycleCoord (2 * w + 1) (cycleLabel (2 * w + 1) source forward (w + 1)) (!forward) x =
      reverseCoord w (cycleCoord (2 * w + 1) source forward x) := by
  conv_lhs => arg 4; rw [← cycleLabel_coord hs hx forward]
  exact cycleCoord_rebase (show w + 1 < 2 * w + 1 by omega)
    (cycleCoord_lt (by omega) forward) forward

theorem reverseCoord_eq {w k : Nat} (hw : 2 ≤ w) (hk : k < 2 * w + 1) :
    reverseCoord w k = if k ≤ w + 1 then w + 1 - k else 3 * w + 2 - k := by
  unfold reverseCoord rotate reflect
  rw [Nat.add_mod_mod]
  split_ifs with h
  · rw [show w + 1 + (2 * w + 1 - k) = (2 * w + 1) + (w + 1 - k) by omega]
    simp [Nat.mod_eq_of_lt (show w + 1 - k < 2 * w + 1 by omega)]
  · rw [Nat.mod_eq_of_lt (show w + 1 + (2 * w + 1 - k) < 2 * w + 1 by omega)]
    omega

theorem foldedIndex_reverse_iff {w a b : Nat} (hw : 2 ≤ w)
    (ha : a < 2 * w + 1) (hb : b < 2 * w + 1)
    (hab : cycleAdjacent (2 * w + 1) a b = true) :
    foldedIndex w a < foldedIndex w b ↔
      foldedIndex w (reverseCoord w b) < foldedIndex w (reverseCoord w a) := by
  have he := (cycleAdjacent_iff ha hb).mp hab
  rw [reverseCoord_eq hw ha, reverseCoord_eq hw hb]
  unfold foldedIndex
  split_ifs <;> omega

end OddCycle
