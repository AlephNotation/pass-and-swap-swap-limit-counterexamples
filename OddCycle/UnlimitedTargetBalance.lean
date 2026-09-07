import OddCycle.TargetOccurrences
import OddCycle.TargetWeights
import Mathlib.Tactic.FieldSimp

/-! Unlimited stationary balance at the target, derived from all of its
predecessors rather than imported as an unproved product-form theorem. -/

namespace OddCycle

variable {K : Type*} [Field K]

theorem spike_total_event_rate {w : Nat} {s : State} (hv : Valid (2 * w + 1) s)
    (theta : K) (budget : Nat) :
    ((events (cycleAdjacent (2 * w + 1)) budget s).map (fun e => spikeRate theta e.2)).sum = theta + (2 * w : Nat) := by
  calc
    _ = (((events (cycleAdjacent (2 * w + 1)) budget s).map Prod.snd).map (spikeRate theta)).sum := by
      simp only [List.map_map, Function.comp_def]
    _ = ((s.1 ++ s.2).map (spikeRate theta)).sum := by rw [events_initiating]
    _ = ((List.range (2 * w + 1)).map (spikeRate theta)).sum := (hv.map _).sum_eq
    _ = _ := by simp [List.range_succ_eq_map, List.map_map, Function.comp_def, spikeRate, List.sum_replicate]

theorem balance_spike_at {w : Nat} (hw : 2 ≤ w) (theta : K) (budget : Nat) (weight : State → K) (target : State) (ht : target ∈ balancedStates w) :
    balance (cycleAdjacent (2 * w + 1)) budget (spikeRate theta) (balancedStates w) weight target =
      ((balancedStates w).map (fun s => incomingRow (cycleAdjacent (2 * w + 1)) budget
        (spikeRate theta) (weight s) target s)).sum - weight target * (theta + (2 * w : Nat)) := by
  have hout (s : State) (hs : s ∈ balancedStates w) :
      ((events (cycleAdjacent (2 * w + 1)) budget s).map
        (fun e => if s = target then weight s * spikeRate theta e.2 else 0)).sum =
        if s = target then weight target * (theta + (2 * w : Nat)) else 0 := by
    by_cases he : s = target
    · subst s
      simp only [↓reduceIte, List.sum_map_mul_left]
      rw [spike_total_event_rate ((mem_balancedStates_iff hw _).mp hs).1 theta budget]
    · simp [he]
  unfold balance
  simp only [sum_map_sub]
  have heq := List.map_congr_left hout
  rw [heq, sum_map_single (balancedStates_nodup hw)]
  simp only [ht, ↓reduceIte, incomingRow]

theorem balance_spike_incoming {w : Nat} (hw : 2 ≤ w) (theta : K) (budget : Nat) (weight : State → K) :
    balance (cycleAdjacent (2 * w + 1)) budget (spikeRate theta) (balancedStates w) weight (flowTarget w) =
      ((balancedStates w).map (fun s => incomingRow (cycleAdjacent (2 * w + 1)) budget
        (spikeRate theta) (weight s) (flowTarget w) s)).sum - weight (flowTarget w) * (theta + (2 * w : Nat)) :=
  balance_spike_at hw theta budget weight (flowTarget w)
    ((mem_balancedStates_iff hw _).mpr (flowTarget_valid_balanced hw))

theorem unlimited_target_incoming {w : Nat} (hw : 2 ≤ w) (theta : K) :
    ((balancedStates w).map (fun s => incomingRow (cycleAdjacent (2 * w + 1)) (2 * w + 1)
      (spikeRate theta) (canonicalWeight (spikeRate theta) s) (flowTarget w) s)).sum =
      (theta⁻¹ * (theta + 1)⁻¹ * ((2 * w - 1).factorial : K)⁻¹) * (theta + 1) +
      (((2 * w).factorial : K)⁻¹ * (theta + (2 * w : Nat))⁻¹) * (theta + (2 * w : Nat)) := by
  rw [← incomingOccurrences_sum]
  rw [((targetOccurrences_complete hw).map (fun o => canonicalWeight (spikeRate theta) o.source * spikeRate theta o.initiating)).sum_eq]
  unfold targetOccurrences
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, List.map_map, Function.comp_def]
  rw [firstFlowSource_weight hw theta]
  rw [show spikeRate theta 0 = theta by simp [spikeRate],
    show spikeRate theta (2 * w) = 1 by simp [spikeRate, show 2 * w ≠ 0 by omega], mul_one]
  have heq : ((List.range (2 * w + 1)).map (fun pos =>
      canonicalWeight (spikeRate theta) (secondFlowSource w pos) * spikeRate theta (secondFlowInitiating w pos))) =
      (List.range (2 * w + 1)).map (fun pos =>
        (((2 * w).factorial : K)⁻¹ * (theta + (2 * w : Nat))⁻¹) * (if pos = 2 * w then theta else 1)) := by
    apply List.map_congr_left
    intro p hp
    have hp' : p ≤ 2 * w := by have := List.mem_range.mp hp; omega
    rw [secondFlowSource_weight hw hp' theta, secondFlowInitiating_rate hw hp' theta]
  rw [heq, List.range_succ, List.map_append, List.sum_append]
  have hmap : ((List.range (2 * w)).map (fun pos =>
      (((2 * w).factorial : K)⁻¹ * (theta + (2 * w : Nat))⁻¹) * (if pos = 2 * w then theta else 1))) =
      (List.range (2 * w)).map (fun _ => ((2 * w).factorial : K)⁻¹ * (theta + (2 * w : Nat))⁻¹) := by
    apply List.map_congr_left
    intro p hp
    simp only [if_neg (show p ≠ 2 * w by have := List.mem_range.mp hp; omega), mul_one]
  rw [hmap]
  simp only [List.map_const', List.sum_replicate, List.length_range, nsmul_eq_mul,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ↓reduceIte, add_zero]
  ring

theorem unlimited_target_balance [CharZero K] {w : Nat} (hw : 2 ≤ w) (theta : K)
    (ht : theta ≠ 0) (ht1 : theta + 1 ≠ 0) (htn : theta + (2 * w : Nat) ≠ 0) :
    balance (cycleAdjacent (2 * w + 1)) (2 * w + 1) (spikeRate theta) (balancedStates w)
      (canonicalWeight (spikeRate theta)) (flowTarget w) = 0 := by
  rw [balance_spike_incoming hw theta, unlimited_target_incoming hw theta, flowTarget_weight hw theta]
  have hf : (((2 * w).factorial : Nat) : K) = (2 * w : Nat) * (((2 * w - 1).factorial : Nat) : K) := by
    have hnat : (2 * w).factorial = (2 * w) * (2 * w - 1).factorial := by
      conv_lhs => rw [show 2 * w = (2 * w - 1) + 1 by omega, Nat.factorial_succ]
      congr 1
      omega
    simpa only [Nat.cast_mul] using congrArg (fun n : Nat => (n : K)) hnat
  have hn : (2 * w : K) ≠ 0 := by exact_mod_cast (show 2 * w ≠ 0 by omega)
  have hwK : (w : K) ≠ 0 := by exact_mod_cast (show w ≠ 0 by omega)
  have hprev : (((2 * w - 1).factorial : Nat) : K) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * w - 1)
  rw [hf]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at htn ⊢
  field_simp [hwK]
  ring

end OddCycle
