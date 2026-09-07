import OddCycle.FlowWords

/-! The coordinate source words equal the explicit words printed in the paper. -/

namespace OddCycle

theorem middle_label_true {w k : Nat} (hk : k ≤ w) :
    cycleLabel (2 * w + 1) w true k = w + k := by
  simp [cycleLabel, Nat.mod_eq_of_lt (show w + k < 2 * w + 1 by omega)]

theorem middle_label_false {w k : Nat} (hk : k ≤ w) :
    cycleLabel (2 * w + 1) w false k = w - k := by
  have he : w + (2 * w + 1 - k) = (2 * w + 1) + (w - k) := by omega
  simp [cycleLabel, he, Nat.mod_eq_of_lt (show w - k < 2 * w + 1 by omega)]

theorem shortInterior_middle_true {w : Nat} (hw : 2 ≤ w) :
    shortInterior w w true = (List.range' 1 (w - 1)).reverse := by
  rw [shortInterior_eq_range' hw, List.reverse_range']
  simp only [Bool.not_true, List.range'_eq_map_range, List.map_map]
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp hj
  simp only [Function.comp_apply]
  rw [middle_label_false (by omega)]
  omega

theorem shortInterior_middle_false {w : Nat} (hw : 2 ≤ w) :
    shortInterior w w false = List.range' (w + 1) (w - 1) := by
  rw [shortInterior_eq_range' hw]
  simp only [Bool.not_false, List.range'_eq_map_range, List.map_map]
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp hj
  simp only [Function.comp_apply]
  rw [middle_label_true (by omega)]
  omega

theorem longInterior_middle_false (w : Nat) :
    longInterior w w false = (List.range w).reverse := by
  unfold longInterior
  conv_rhs => rw [List.range_eq_range', List.reverse_range']
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.mp hj
  rw [middle_label_false (by omega)]
  omega

theorem flowQueue_labels {w : Nat} (hw : 2 ≤ w) :
    flowQueue w = (List.range' 1 w).reverse ++ List.range' (w + 1) w := by
  have hleft : (List.range' 1 w).reverse = w :: (List.range' 1 (w - 1)).reverse := by
    have he : List.range' 1 w = List.range' 1 (w - 1) ++ [w] := by
      conv_lhs => rw [show w = (w - 1) + 1 by omega, List.range'_concat]
      congr 2
      omega
    rw [he, List.reverse_append]
    rfl
  have hright : List.range' (w + 1) w = List.range' (w + 1) (w - 1) ++ [2 * w] := by
    conv_lhs => rw [show w = (w - 1) + 1 by omega, List.range'_concat]
    congr 2 <;> omega
  simp [flowQueue, flowCore, shortInterior_middle_true hw, shortInterior_middle_false hw,
    hleft, hright, List.append_assoc]

theorem flowWordX_labels {w : Nat} (hw : 2 ≤ w) :
    flowWordX w = (List.range (w + 1)).reverse ++ List.range' (w + 1) w := by
  rw [flowWordX, branchWord_eq_interiors, (flow_endpoints hw).2.1,
    longInterior_middle_false w, shortInterior_middle_false hw, List.range_succ, List.reverse_append]
  have he : List.range' (w + 1) w = List.range' (w + 1) (w - 1) ++ [2 * w] := by
    conv_lhs => rw [show w = (w - 1) + 1 by omega, List.range'_concat]
    congr 2 <;> omega
  simp [he, List.append_assoc]

theorem flowWordY_labels {w : Nat} (hw : 2 ≤ w) :
    flowWordY w = w :: (w + 1) ::
      ((List.range' 1 (w - 1)).reverse ++ List.range' (w + 2) (w - 1)) ++ [0] := by
  have htail : (List.range' 2 (w - 1)).map (cycleLabel (2 * w + 1) w true) =
      List.range' (w + 2) (w - 1) := by
    simp only [List.range'_eq_map_range, List.map_map]
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    simp only [Function.comp_apply]
    rw [middle_label_true (by omega)]
    omega
  simp [flowWordY, middle_label_true (show 1 ≤ w by omega), shortInterior_middle_true hw, htail]

end OddCycle
