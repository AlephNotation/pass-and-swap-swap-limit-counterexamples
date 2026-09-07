import OddCycle.CycleCoordinates

/-! A surjective proper coloring by exactly w+1 colors. -/

namespace OddCycle

def partiteColor (w i : Nat) : Nat := i % (w + 1)

theorem partiteColor_lt (w i : Nat) : partiteColor w i < w + 1 := Nat.mod_lt _ (by omega)

theorem partiteColor_eq {w i : Nat} (hi : i < 2 * w + 1) :
    partiteColor w i = if i ≤ w then i else i - (w + 1) := by
  unfold partiteColor
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [Nat.mod_eq_sub_mod (by omega : w + 1 ≤ i), Nat.mod_eq_of_lt (by omega : i - (w + 1) < w + 1)]

theorem partiteColor_proper {w i j : Nat} (hw : 2 ≤ w) (hi : i < 2 * w + 1) (hj : j < 2 * w + 1)
    (hadj : cycleAdjacent (2 * w + 1) i j = true) : partiteColor w i ≠ partiteColor w j := by
  have he := (cycleAdjacent_iff hi hj).mp hadj
  rw [partiteColor_eq hi, partiteColor_eq hj]
  split_ifs <;> omega

theorem partiteColor_surjective {w : Nat} (hw : 2 ≤ w) {c : Nat} (hc : c < w + 1) :
    ∃ i < 2 * w + 1, partiteColor w i = c :=
  ⟨c, by omega, Nat.mod_eq_of_lt hc⟩

end OddCycle
