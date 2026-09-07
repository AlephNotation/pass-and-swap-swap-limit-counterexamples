import OddCycle.ClosedClasses
import OddCycle.QueueLengthDynamics

/-! Every closed communicating class contains all cuts of each of its placement
words. Consequently, weights depending only on queue length have the same
normalized length marginal on every class. -/

noncomputable section

namespace OddCycle

open Finset

theorem ClosedClass.cut_mem {n w : Nat} {states : List State}
    (hc : ClosedClass n w states) {s : State} (hs : s ∈ states) (k : Nat) :
    cutState (placement s) k ∈ states :=
  hc.reachable hs (reachable_of_placement_eq (placement_cutState _ _).symm)

theorem ClosedClass.word_length {n w : Nat} {states : List State}
    (hc : ClosedClass n w states) {q : Queue} (hq : q ∈ states.toFinset.image placement) :
    q.length = n := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
  simpa only [List.length_range] using (hc.valid s (List.mem_toFinset.mp hs)).placement_perm.length_eq

/-- A class is exactly its set of placement words times the possible cuts. -/
def ClosedClass.wordCutEquiv {n w : Nat} {states : List State}
    (hc : ClosedClass n w states) :
    ↥states.toFinset ≃ ↥(states.toFinset.image placement) × Fin (n + 1) where
  toFun s := (⟨placement s.val, Finset.mem_image.mpr ⟨s.val, s.property, rfl⟩⟩,
    ⟨s.val.1.length, by
      have h := (hc.valid s.val (List.mem_toFinset.mp s.property)).length_eq
      simp only [List.length_append, List.length_range] at h
      omega⟩)
  invFun p := ⟨cutState p.1.val p.2.val, by
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp p.1.property
    rw [← he]
    exact List.mem_toFinset.mpr (hc.cut_mem (List.mem_toFinset.mp hs) _)⟩
  left_inv s := Subtype.ext (cutState_placement s.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (placement_cutState _ _)
    · apply Fin.ext
      change (p.1.val.take p.2.val).length = p.2.val
      rw [List.length_take, Nat.min_eq_left]
      have hh := hc.word_length p.1.property
      have hk := p.2.isLt
      omega

theorem ClosedClass.length_weight_sum {n w : Nat} {states : List State}
    (hc : ClosedClass n w states) (r : Nat → ℝ) :
    (∑ s : ↥states.toFinset, r s.val.1.length) =
      (states.toFinset.image placement).card * ∑ k : Fin (n + 1), r k.val := by
  rw [Fintype.sum_equiv hc.wordCutEquiv (fun s => r s.val.1.length)
    (fun p => r p.2.val) (fun _ => rfl)]
  simp [Fintype.sum_prod_type]

theorem ClosedClass.length_weight_at {n w : Nat} {states : List State}
    (hc : ClosedClass n w states) (r : Nat → ℝ) (k : Fin (n + 1)) :
    (∑ s : ↥states.toFinset, if s.val.1.length = k.val then r s.val.1.length else 0) =
      (states.toFinset.image placement).card * r k.val := by
  rw [hc.length_weight_sum (fun j => if j = k.val then r j else 0)]
  congr 1
  simpa only [Fin.val_inj, Finset.mem_univ, if_true] using
    (Finset.sum_ite_eq' Finset.univ k (fun j : Fin (n + 1) => r j.val))

/-- This marginal identity does not assert stationarity of the full weight. -/
theorem ClosedClass.normalized_length_marginal {n w : Nat} {states : List State}
    (hc : ClosedClass n w states) (r : Nat → ℝ) (k : Fin (n + 1)) :
    (∑ s : ↥states.toFinset, if s.val.1.length = k.val then r s.val.1.length else 0) /
      (∑ s : ↥states.toFinset, r s.val.1.length) =
      r k.val / ∑ j : Fin (n + 1), r j.val := by
  have hne : (states.toFinset.image placement).Nonempty := by
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil states hc.nonempty
    exact ⟨placement s, Finset.mem_image.mpr ⟨s, List.mem_toFinset.mpr hs, rfl⟩⟩
  have hcard : ((states.toFinset.image placement).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  rw [hc.length_weight_at, hc.length_weight_sum]
  exact mul_div_mul_left _ _ hcard

/-- Reciprocal prefix capacities of a queue containing `k` jobs. -/
def lengthWeight (μ : Nat → ℝ) : Nat → ℝ
  | 0 => 1
  | k + 1 => lengthWeight μ k * (μ (k + 1))⁻¹

theorem byLengthCapacity_weight (μ : Nat → ℝ) (hμ : μ 0 = 0) (q : Queue) :
    (byLengthCapacity μ hμ).weight q = lengthWeight μ q.length := by
  induction q using List.reverseRecOn with
  | nil => rfl
  | append_singleton q x ih =>
    rw [OICapacity.weight_append_singleton, ih]
    simp only [byLengthCapacity, List.length_append, List.length_singleton, lengthWeight]

def lengthCanonicalWeight (n : Nat) (μ ν : Nat → ℝ) (k : Nat) : ℝ :=
  lengthWeight μ k * lengthWeight ν (n - k)

theorem oiCanonicalWeight_byLength {n : Nat} {s : State} (hs : Valid n s)
    (μ ν : Nat → ℝ) (hμ : μ 0 = 0) (hν : ν 0 = 0) :
    oiCanonicalWeight (byLengthCapacity μ hμ) (byLengthCapacity ν hν) s =
      lengthCanonicalWeight n μ ν s.1.length := by
  have hl := hs.length_eq
  simp only [List.length_append, List.length_range] at hl
  simp only [oiCanonicalWeight, byLengthCapacity_weight, lengthCanonicalWeight,
    show s.2.length = n - s.1.length by omega]

theorem ClosedClass.canonical_length_marginal {n w : Nat} {states : List State}
    (hc : ClosedClass n w states) (μ ν : Nat → ℝ) (hμ : μ 0 = 0) (hν : ν 0 = 0)
    (k : Fin (n + 1)) :
    let W := oiCanonicalWeight (byLengthCapacity μ hμ) (byLengthCapacity ν hν)
    (∑ s : ↥states.toFinset, if s.val.1.length = k.val then W s.val else 0) /
      (∑ s : ↥states.toFinset, W s.val) =
      lengthCanonicalWeight n μ ν k.val / ∑ j : Fin (n + 1), lengthCanonicalWeight n μ ν j.val := by
  dsimp only
  simp_rw [oiCanonicalWeight_byLength (hc.valid _ (List.mem_toFinset.mp (Subtype.property _))) μ ν hμ hν]
  exact hc.normalized_length_marginal (lengthCanonicalWeight n μ ν) k

end OddCycle
