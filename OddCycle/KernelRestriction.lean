import OddCycle.FiniteLumping

/-! Restriction of a finite kernel to a closed embedded state space. -/

noncomputable section

namespace OddCycle.FiniteMarkov

open Finset

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
variable (P : FiniteMarkov T) (e : S ↪ T)
variable (closed : ∀ s t, 0 < P.prob (e s) t → ∃ u, e u = t)

include closed

omit [Fintype S] [DecidableEq T] in
theorem outside_range_zero (s : S) (t : T) (ht : ¬ ∃ u, e u = t) : P.prob (e s) t = 0 :=
  le_antisymm (le_of_not_gt (fun hp => ht (closed s t hp))) (P.nonneg _ _)

def restrictEmbedding : FiniteMarkov S where
  prob s t := P.prob (e s) (e t)
  nonneg s t := P.nonneg _ _
  sum_one s := by
    rw [← Finset.sum_image (fun _ _ _ _ h => e.injective h)]
    calc
      _ = ∑ t, P.prob (e s) t := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro t _ ht
        apply P.outside_range_zero e closed s t
        simpa only [Finset.mem_image, Finset.mem_univ, true_and] using ht
      _ = 1 := P.sum_one _

theorem restrictEmbedding_lumps : (P.restrictEmbedding e closed).LumpsTo P e := by
  classical
  intro s t
  change (∑ u, if e u = t then P.prob (e s) (e u) else 0) = P.prob (e s) t
  by_cases ht : ∃ u, e u = t
  · obtain ⟨u, rfl⟩ := ht
    simp only [EmbeddingLike.apply_eq_iff_eq]
    simp
  · simp only [show ∀ u, e u ≠ t from fun u hu => ht ⟨u, hu⟩, if_false, Finset.sum_const_zero,
      P.outside_range_zero e closed s t ht]

end OddCycle.FiniteMarkov
