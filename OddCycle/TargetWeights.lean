import OddCycle.TargetPredecessors
import OddCycle.PrefixWeights

/-! The target and all of its unlimited predecessors have elementary weights. -/

namespace OddCycle

theorem flowQueue_zero_not_mem {w : Nat} (hw : 2 ≤ w) : 0 ∉ flowQueue w := by
  have hn : (0 :: flowQueue w).Nodup := (flowTarget_valid_balanced hw).1.nodup_iff.mpr List.nodup_range
  exact (List.nodup_cons.mp hn).1

theorem secondFlowSource_ends_zero {w pos : Nat} (hw : 2 ≤ w) (hp : pos ≤ 2 * w) :
    ∃ pre, (secondFlowSource w pos).2 = pre ++ [0] := by
  exact reverseInput_ends_departed (w :: flowCore w) (2 * w) 0 pos
    (by change pos ≤ (flowQueue w).length; rwa [flowQueue_length hw]) (by simp [cycleAdjacent])

theorem secondFlowInitiating_ne_zero {w pos : Nat} (hw : 2 ≤ w) (hp : pos < 2 * w) :
    secondFlowInitiating w pos ≠ 0 := by
  obtain ⟨pre, he⟩ := secondFlowSource_ends_zero hw hp.le
  have hv := (secondFlowSource_valid_balanced hw (pos := pos)).1
  have hl := hv.length_eq
  have hfirst : (secondFlowSource w pos).1 = [] := rfl
  simp only [hfirst, List.nil_append, List.length_range] at hl
  rw [he, List.length_append, List.length_singleton] at hl
  have hpre : pre.length = 2 * w := by omega
  have hn : (pre ++ [0]).Nodup := by
    simpa only [hfirst, List.nil_append, he] using hv.nodup_iff.mpr List.nodup_range
  have hz : 0 ∉ pre := by
    intro hm
    exact (List.nodup_append.mp hn).2.2 0 hm 0 (by simp) rfl
  have ht := transition_initiating (cycleAdjacent (2 * w + 1)) (2 * w + 1) (secondFlowSource w pos) true pos
  rw [secondFlowSource_transition hw hp.le] at ht
  simp only [Option.map_some, ↓reduceIte] at ht
  rw [he, List.getElem?_append_left (by omega : pos < pre.length)] at ht
  intro hi
  rw [hi] at ht
  exact hz (List.mem_of_getElem? ht.symm)

variable {K : Type*} [Field K]

theorem flowTarget_weight {w : Nat} (hw : 2 ≤ w) (theta : K) :
    canonicalWeight (spikeRate theta) (flowTarget w) = theta⁻¹ * ((2 * w).factorial : K)⁻¹ := by
  have hu : ∀ x ∈ flowQueue w, spikeRate theta x = 1 := by
    intro x hx
    have hn : x ≠ 0 := by intro he; subst x; exact flowQueue_zero_not_mem hw hx
    simp [spikeRate, hn]
  simp [canonicalWeight, flowTarget, prefixWeight, spikeRate, prefixWeight_unit _ _ hu, flowQueue_length hw]

theorem firstFlowSource_weight {w : Nat} (hw : 2 ≤ w) (theta : K) :
    canonicalWeight (spikeRate theta) (firstFlowSource w) =
      theta⁻¹ * (theta + 1)⁻¹ * ((2 * w - 1).factorial : K)⁻¹ := by
  have hu : ∀ x ∈ w :: flowCore w, spikeRate theta x = 1 := by
    intro x hx
    have hn : x ≠ 0 := by
      intro he
      subst x
      exact flowQueue_zero_not_mem hw (List.mem_append_left _ hx)
    simp [spikeRate, hn]
  have hl : (w :: flowCore w).length = 2 * w - 1 := by
    have h := flowQueue_length hw
    change ((w :: flowCore w) ++ [2 * w]).length = 2 * w at h
    simp only [List.length_append, List.length_singleton] at h
    omega
  simp [canonicalWeight, firstFlowSource, prefixWeight, spikeRate, show 2 * w ≠ 0 by omega,
    prefixWeight_unit _ _ hu, hl]

theorem secondFlowSource_weight {w pos : Nat} (hw : 2 ≤ w) (hp : pos ≤ 2 * w) (theta : K) :
    canonicalWeight (spikeRate theta) (secondFlowSource w pos) =
      ((2 * w).factorial : K)⁻¹ * (theta + (2 * w : Nat))⁻¹ := by
  apply spike_last_weight_of_valid theta
  · exact (secondFlowSource_valid_balanced hw).1.exchange
  · exact secondFlowSource_ends_zero hw hp

theorem secondFlowInitiating_rate {w pos : Nat} (hw : 2 ≤ w) (hp : pos ≤ 2 * w) (theta : K) :
    spikeRate theta (secondFlowInitiating w pos) = if pos = 2 * w then theta else 1 := by
  by_cases he : pos = 2 * w
  · subst pos
    have hlen := flowQueue_length hw
    simp [secondFlowInitiating, ← hlen, unlimitedCarry, spikeRate]
  · have hne := secondFlowInitiating_ne_zero (pos := pos) hw (by omega)
    simp [spikeRate, hne, he]

end OddCycle
