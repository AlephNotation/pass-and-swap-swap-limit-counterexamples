import OddCycle.OrientationClasses
import OddCycle.OIGenerator

/-! Positive normalized canonical laws on short recurrent classes. -/

namespace OddCycle

variable {K : Type*} [Field K]

theorem oiBalance_scale (adj : Nat → Nat → Bool) (budget : Nat) (μ ν : OICapacity K)
    (states : List State) (weight : State → K) (target : State) (a : K) :
    oiBalance adj budget μ ν states (fun s => a * weight s) target =
      a * oiBalance adj budget μ ν states weight target := by
  simp only [oiBalance, oiIncoming, mul_assoc, List.sum_map_mul_left, mul_sub]

def oiNormalizer (μ ν : OICapacity K) (states : List State) : K :=
  (states.map (oiCanonicalWeight μ ν)).sum

def normalizedOIWeight (μ ν : OICapacity K) (states : List State) (s : State) : K :=
  (oiNormalizer μ ν states)⁻¹ * oiCanonicalWeight μ ν s

theorem normalizedOI_stationary {adj : Nat → Nat → Bool} {budget : Nat} {μ ν : OICapacity K}
    {states : List State} (h : OIStationary adj budget μ ν states (oiCanonicalWeight μ ν)) :
    OIStationary adj budget μ ν states (normalizedOIWeight μ ν states) := by
  intro s hs
  change oiBalance adj budget μ ν states
    (fun t => (oiNormalizer μ ν states)⁻¹ * oiCanonicalWeight μ ν t) s = 0
  rw [oiBalance_scale, h s hs, mul_zero]

theorem normalizedOI_stationary_iff {adj : Nat → Nat → Bool} {budget : Nat} {μ ν : OICapacity K}
    {states : List State} (hn : oiNormalizer μ ν states ≠ 0) :
    OIStationary adj budget μ ν states (normalizedOIWeight μ ν states) ↔
      OIStationary adj budget μ ν states (oiCanonicalWeight μ ν) := by
  constructor
  · intro h s hs
    have he := h s hs
    change oiBalance adj budget μ ν states
      (fun t => (oiNormalizer μ ν states)⁻¹ * oiCanonicalWeight μ ν t) s = 0 at he
    rw [oiBalance_scale] at he
    exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero hn)
  · exact normalizedOI_stationary

theorem normalizedOI_sum {μ ν : OICapacity K} {states : List State}
    (h : oiNormalizer μ ν states ≠ 0) :
    (states.map (normalizedOIWeight μ ν states)).sum = 1 := by
  change (states.map (fun s => (oiNormalizer μ ν states)⁻¹ * oiCanonicalWeight μ ν s)).sum = 1
  rw [List.sum_map_mul_left]
  exact inv_mul_cancel₀ h

theorem oiCanonicalWeight_pos {n : Nat} (μ ν : PositiveOIAllocation n) {s : State} (hs : Valid n s) :
    0 < oiCanonicalWeight μ.toOICapacity ν.toOICapacity s :=
  mul_pos (μ.weight_pos hs.first_subperm) (ν.weight_pos hs.second_subperm)

theorem oiNormalizer_pos {n : Nat} (μ ν : PositiveOIAllocation n) {states : List State}
    (hv : ∀ s ∈ states, Valid n s) (hne : states ≠ []) :
    0 < oiNormalizer μ.toOICapacity ν.toOICapacity states := by
  apply List.sum_pos
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact oiCanonicalWeight_pos μ ν (hv s hs)
  · simpa using hne

theorem normalizedOI_pos {n : Nat} (μ ν : PositiveOIAllocation n) {states : List State}
    (hv : ∀ s ∈ states, Valid n s) {s : State} (hs : s ∈ states) :
    0 < normalizedOIWeight μ.toOICapacity ν.toOICapacity states s := by
  have hne : states ≠ [] := by intro he; simp [he] at hs
  exact mul_pos (inv_pos.mpr (oiNormalizer_pos μ ν hv hne)) (oiCanonicalWeight_pos μ ν (hv s hs))

theorem short_class_normalized_oi {n w : Nat} (hn : 0 < n) (μ ν : PositiveOIAllocation n)
    {s : State} (hs : Valid n s) (hw : height n s ≤ w) :
    let states := orientationStates n (orientation n s)
    let W := normalizedOIWeight μ.toOICapacity ν.toOICapacity states
    OIStationary (cycleAdjacent n) w μ.toOICapacity ν.toOICapacity states W ∧
      (states.map W).sum = 1 ∧ ∀ t ∈ states, 0 < W t := by
  dsimp only
  have hs' : s ∈ orientationStates n (orientation n s) := mem_orientationStates.mpr ⟨hs, rfl⟩
  have hv := (orientationStates_support n (orientation n s)).valid
  have hn' : orientationStates n (orientation n s) ≠ [] := by intro he; simp [he] at hs'
  exact ⟨normalizedOI_stationary (orientation_class_oi_stationary hn μ ν hs hw),
    normalizedOI_sum (oiNormalizer_pos μ ν hv hn').ne', fun t ht => normalizedOI_pos μ ν hv ht⟩

end OddCycle
