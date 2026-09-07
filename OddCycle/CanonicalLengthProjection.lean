import OddCycle.ClassLengthKernel

/-! The normalized canonical candidate and the actual stationary probability
vector have exactly the same length marginal on every closed cycle class. -/

noncomputable section

namespace OddCycle.ClosedClass

open Finset

variable {n w : Nat} {states : List State} (hc : ClosedClass n w states)

include hc

theorem state_sum (f : State → ℝ) : (∑ s : ClassState states, f s.val) = (states.map f).sum := by
  rw [← Finset.sum_subtype states.toFinset (fun _ => Iff.rfl) f]
  exact List.sum_toFinset f hc.nodup

def unitCanonical (s : ClassState states) : ℝ :=
  normalizedOIWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity states (hc.embedding s).val

theorem unitCanonical_simplex : hc.unitCanonical ∈ stdSimplex ℝ (ClassState states) := by
  constructor
  · intro s
    exact (normalizedOI_pos (unitAllocation n) (unitAllocation n) hc.valid (List.mem_toFinset.mp s.property)).le
  · change (∑ s : ClassState states,
      normalizedOIWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity states s.val) = 1
    rw [hc.state_sum]
    exact normalizedOI_sum (oiNormalizer_pos (unitAllocation n) (unitAllocation n) hc.valid hc.nonempty).ne'

theorem unitCanonical_length_observables (f : Nat → ℝ) :
    (∑ s : ClassState states, hc.unitCanonical s *
      lengthGenerator (cycleAdjacent n) w (fun _ => 1) (fun _ => 1) s.val f) = 0 := by
  have h := hc.canonical_length_observables (fun j => (j : ℝ)) (fun j => (j : ℝ)) (by simp) (by simp)
    (fun j hj _ => by change (j : ℝ) ≠ 0; exact_mod_cast (by omega : j ≠ 0))
    (fun j hj _ => by change (j : ℝ) ≠ 0; exact_mod_cast (by omega : j ≠ 0)) f
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left] at h
  rw [← unitAllocation_byLength n] at h
  simp only [unitCanonical, embedding_val, normalizedOIWeight, mul_assoc, ← Finset.mul_sum, h, mul_zero]

theorem unitCanonical_projected_stationary (hn : 0 < n) :
    (hc.lengthKernel hn).StationaryVector (FiniteMarkov.push hc.queueLength hc.unitCanonical) := by
  apply (hc.unitKernel_lumps hn).stationary_of_observables
  intro g
  let f : Nat → ℝ := fun k => if hk : k < n + 1 then g ⟨k, hk⟩ else 0
  have hf (s : ClassState states) : f s.val.1.length = g (hc.queueLength s) := by
    have hlen := (hc.queueLength s).isLt
    change s.val.1.length < n + 1 at hlen
    simp only [f, dif_pos hlen]
    rfl
  have hfun : (fun s : ClassState states => f s.val.1.length) = g ∘ hc.queueLength := by
    funext s
    exact hf s
  have hgen (s : ClassState states) :
      (n : ℝ) * ((hc.unitKernel hn).expect (g ∘ hc.queueLength) s - g (hc.queueLength s)) =
        lengthGenerator (cycleAdjacent n) w (fun _ => 1) (fun _ => 1) s.val f := by
    have h := hc.unitKernel_generator hn s f
    rwa [hfun, hf s] at h
  have hh : (n : ℝ) * (∑ s : ClassState states, hc.unitCanonical s *
      ((hc.unitKernel hn).expect (g ∘ hc.queueLength) s - g (hc.queueLength s))) = 0 := by
    calc
      _ = ∑ s : ClassState states, hc.unitCanonical s *
          ((n : ℝ) * ((hc.unitKernel hn).expect (g ∘ hc.queueLength) s - g (hc.queueLength s))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = _ := by simp_rw [hgen]; exact hc.unitCanonical_length_observables f
  exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast hn.ne')

theorem unitCanonical_same_marginal (hn : 0 < n) {π : ClassState states → ℝ}
    (hπ : π ∈ stdSimplex ℝ (ClassState states)) (hstat : (hc.unitKernel hn).StationaryVector π) :
    FiniteMarkov.push hc.queueLength hc.unitCanonical = FiniteMarkov.push hc.queueLength π :=
  (hc.lengthKernel hn).stationary_unique (hc.lengthKernel_irreducible hn)
    (FiniteMarkov.push_simplex _ hc.unitCanonical_simplex) (FiniteMarkov.push_simplex _ hπ)
    (hc.unitCanonical_projected_stationary hn) ((hc.unitKernel_lumps hn).push_stationary hstat)

theorem unit_stationary_exists (hn : 0 < n) :
    ∃ π ∈ stdSimplex ℝ (ClassState states), (hc.unitKernel hn).StationaryVector π := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil states hc.nonempty
  letI : Nonempty (ClassState states) := ⟨⟨s, List.mem_toFinset.mpr hs⟩⟩
  exact (hc.unitKernel hn).stationary_exists

end OddCycle.ClosedClass
