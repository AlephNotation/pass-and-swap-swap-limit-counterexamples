import OddCycle.OrientationQuotient
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-! Adding reversible graph symmetries to a finite directed graph does not
change which vertices belong to terminal components. The proof counts the
vertices reachable in the original graph, not in the augmented graph. -/

namespace OddCycle.ReachabilityQuotient

variable {S : Type*} (step : S → S → Prop)

def Preserves (e : S ≃ S) : Prop := ∀ x y, step (e x) (e y) ↔ step x y

theorem preserves_reach {e : S ≃ S} (he : Preserves step e) (x y : S) :
    Reach step (e x) (e y) ↔ Reach step x y := by
  constructor
  · intro h
    have hh := Relation.ReflTransGen.lift e.symm (fun a b hab =>
      (he (e.symm a) (e.symm b)).mp (by simpa using hab)) h
    simpa using hh
  · exact Relation.ReflTransGen.lift e (fun a b hab => (he a b).mpr hab)

theorem preserves_terminal {e : S ≃ S} (he : Preserves step e) {x : S}
    (hx : Terminal step x) : Terminal step (e x) := by
  intro y hy
  have hxy : Reach step x (e.symm y) :=
    (preserves_reach step he x (e.symm y)).mp (by simpa using hy)
  have hh := (preserves_reach step he (e.symm y) x).mpr (hx _ hxy)
  simpa using hh

noncomputable def reachableSet [Fintype S] (x : S) : Finset S := by
  classical
  exact Finset.univ.filter (Reach step x)

@[simp] theorem mem_reachableSet [Fintype S] (x y : S) :
    y ∈ reachableSet step x ↔ Reach step x y := by
  classical
  simp [reachableSet]

theorem reachableSet_subset [Fintype S] {x y : S} (h : Reach step x y) :
    reachableSet step y ⊆ reachableSet step x := by
  intro z hz
  exact (mem_reachableSet step x z).mpr (h.trans ((mem_reachableSet step y z).mp hz))

theorem return_of_reachable_card_le [Fintype S] {x y : S} (h : Reach step x y)
    (hc : (reachableSet step x).card ≤ (reachableSet step y).card) : Reach step y x := by
  have he := Finset.eq_of_subset_of_card_le (reachableSet_subset step h) hc
  have hx : x ∈ reachableSet step x := (mem_reachableSet step x x).mpr .refl
  rw [← he] at hx
  exact (mem_reachableSet step y x).mp hx

theorem preserves_reachable_card [Fintype S] {e : S ≃ S} (he : Preserves step e) (x : S) :
    (reachableSet step (e x)).card = (reachableSet step x).card := by
  classical
  symm
  apply Finset.card_bijective e e.bijective
  intro y
  simpa only [mem_reachableSet] using (preserves_reach step he x y).symm

def Augment (symmetry : S → S → Prop) (x y : S) : Prop := step x y ∨ symmetry x y

theorem augment_reach (symmetry : S → S → Prop) {x y : S} (h : Reach step x y) :
    Reach (Augment step symmetry) x y :=
  Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) h

/-- The extra edges may be any symmetric family of graph automorphisms;
there is no assumption that their endpoints already communicate. -/
theorem terminal_augment_iff [Fintype S] (symmetry : S → S → Prop)
    (hsym : ∀ x y, symmetry x y → symmetry y x)
    (hauto : ∀ x y, symmetry x y → ∃ e : S ≃ S, Preserves step e ∧ e x = y)
    (x : S) : Terminal (Augment step symmetry) x ↔ Terminal step x := by
  constructor
  · intro ht y hy
    have hback := ht y (augment_reach step symmetry hy)
    have hmono {a b : S} (h : Augment step symmetry a b) :
        (reachableSet step b).card ≤ (reachableSet step a).card := by
      rcases h with h | h
      · exact Finset.card_le_card (reachableSet_subset step (.single h))
      · obtain ⟨e, he, rfl⟩ := hauto a b h
        exact (preserves_reachable_card step he a).le
    have hc : (reachableSet step x).card ≤ (reachableSet step y).card := by
      clear ht hy
      induction hback with
      | refl => exact le_rfl
      | tail _ hs ih => exact (hmono hs).trans ih
    exact return_of_reachable_card_le step hy hc
  · intro ht y hy
    have hreturn : Terminal step y ∧ Reach (Augment step symmetry) y x := by
      induction hy with
      | refl => exact ⟨ht, .refl⟩
      | @tail a b _ hab ih =>
        rcases hab with hab | hab
        · have hb : Terminal step b := by
            intro c hbc
            exact (ih.1 c ((Relation.ReflTransGen.single hab).trans hbc)).tail hab
          exact ⟨hb, (augment_reach step symmetry (ih.1 b (.single hab))).trans ih.2⟩
        · obtain ⟨e, he, heb⟩ := hauto a b hab
          have hba : Augment step symmetry b a := Or.inr (hsym a b hab)
          refine ⟨?_, (Relation.ReflTransGen.single hba).trans ih.2⟩
          simpa only [heb] using preserves_terminal step he ih.1
    exact hreturn.2

end OddCycle.ReachabilityQuotient
