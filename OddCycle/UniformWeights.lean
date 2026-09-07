import OddCycle.FlowWordLabels
import OddCycle.PrefixWeights

/-! The two canonical source weights, with an arbitrary distinguished rate. -/

namespace OddCycle

variable {K : Type*} [Field K]

def shiftedProduct (w : Nat) (theta : K) : K :=
  ((List.range (w + 1)).map (fun j : Nat => theta + (w : K) + (j : K))).prod

theorem flowSourceX_weight {w : Nat} (hw : 2 ≤ w) (theta : K) :
    canonicalWeight (spikeRate theta) (flowSourceX w) = (w.factorial : K)⁻¹ * (shiftedProduct w theta)⁻¹ := by
  let a := (List.range' 1 w).reverse
  let b := List.range' (w + 1) w
  have hword : flowWordX w = a ++ 0 :: b := by
    have hr : List.range (w + 1) = 0 :: List.range' 1 w := by
      simp [List.range_succ_eq_map, List.range'_eq_map_range, Nat.add_comm]
    rw [flowWordX_labels hw, hr, List.reverse_cons, List.append_assoc]
    rfl
  have ha : 0 ∉ a := by simp [a]
  have hb : 0 ∉ b := by simp [b]
  have he := prefixWeight_spike_between theta a b ha hb
  simpa [canonicalWeight, flowSourceX, prefixWeight, hword, a, b, shiftedProduct] using he

theorem flowSourceY_weight {w : Nat} (hw : 2 ≤ w) (theta : K) :
    canonicalWeight (spikeRate theta) (flowSourceY w) =
      ((2 * w).factorial : K)⁻¹ * (theta + (2 * w : Nat))⁻¹ := by
  apply spike_last_weight_of_valid theta (flowY_frame hw).1
  exact ⟨w :: cycleLabel (2 * w + 1) w true 1 ::
    (shortInterior w w true ++ (List.range' 2 (w - 1)).map (cycleLabel (2 * w + 1) w true)), rfl⟩

theorem shiftedProduct_range (w : Nat) (theta : K) :
    shiftedProduct w theta = ((List.range' w (w + 1)).map (fun k : Nat => theta + (k : K))).prod := by
  simp [shiftedProduct, List.range'_eq_map_range, List.map_map, Function.comp_def, add_assoc]

end OddCycle
