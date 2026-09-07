import OddCycle.ClosedRecurrence
import OddCycle.ShortOrientation
import Mathlib.Data.Fintype.List

/-! Terminal event components and finite-step return probabilities. The
probabilistic conclusion uses the existing stochastic-matrix construction;
it is not a redefinition of recurrence as a graph predicate. -/

namespace OddCycle

namespace FiniteMarkov

open Filter Topology

theorem terminal_returnBy_tendsto_one {S : Type*} [Fintype S] [DecidableEq S]
    (P : FiniteMarkov S) (s : S)
    (ht : ReachabilityQuotient.Terminal (fun a b => 0 < P.prob a b) s) :
    Tendsto (P.returnBy s) atTop (𝓝 1) := by
  classical
  let A : S → Prop := P.Reachable s
  have hc : ∀ i, A i → ∀ j, ¬ A j → P.prob i j = 0 := by
    intro i hi j hj
    apply le_antisymm _ (P.nonneg i j)
    by_contra hn
    exact hj (hi.tail (lt_of_not_ge hn))
  let Q := P.restrict A hc
  let target : {i // A i} := ⟨s, .refl⟩
  have hreach : ∀ i : {i // A i}, Q.Reachable i target := by
    intro i
    have hr := ht i.val i.property
    have liftPath : ∀ {j : S}, P.Reachable i.val j →
        ∀ hj : A j, Q.Reachable i ⟨j, hj⟩ := by
      intro j path
      induction path with
      | refl => intro _; exact .refl
      | @tail j k path hstep ih =>
        intro hk
        have hj : A j := i.property.trans path
        exact (ih hj).tail hstep
    exact liftPath hr (.refl)
  have hlim := Q.returnBy_tendsto_one target hreach
  have he : Q.returnBy target = P.returnBy s := by
    funext n
    exact P.restrict_returnBy A hc target n
  rwa [he] at hlim

end FiniteMarkov

namespace CycleState

noncomputable instance (n : Nat) : Fintype (CycleState n) :=
  Fintype.ofInjective
    (fun s : CycleState n => (⟨s.val, mem_allStates_iff.mpr s.property⟩ : {s // s ∈ allStates n}))
    (fun _ _ he => Subtype.ext (congrArg (fun x : {s // s ∈ allStates n} => x.val) he))

/-- A kernel with positive probabilities on every legal completion has
return probability one at every terminal event state. Self steps are allowed. -/
theorem terminal_returnBy_tendsto_one {n w : Nat} (P : FiniteMarkov (CycleState n))
    (hsupport : ∀ s t, 0 < P.prob s t → Step n w s t ∨ s = t)
    (hpositive : ∀ s t, Step n w s t → 0 < P.prob s t)
    (s : CycleState n) (ht : ReachabilityQuotient.Terminal (Step n w) s) :
    Filter.Tendsto (P.returnBy s) Filter.atTop (nhds 1) := by
  apply P.terminal_returnBy_tendsto_one s
  intro t hst
  have hforward : Relation.ReflTransGen (Step n w) s t := by
    apply Relation.ReflTransGen.lift' id ?_ hst
    intro a b hab
    rcases hsupport a b hab with he | rfl
    · exact .single he
    · exact .refl
  exact Relation.ReflTransGen.lift id (fun a b hab => hpositive a b hab) (ht t hforward)

theorem short_returnBy_tendsto_one {n w : Nat} (hn : 0 < n) (P : FiniteMarkov (CycleState n))
    (hsupport : ∀ s t, 0 < P.prob s t → Step n w s t ∨ s = t)
    (hpositive : ∀ s t, Step n w s t → 0 < P.prob s t)
    (s : CycleState n) (hs : height n s.val ≤ w) :
    Filter.Tendsto (P.returnBy s) Filter.atTop (nhds 1) :=
  terminal_returnBy_tendsto_one P hsupport hpositive s (OddCycle.short_terminal hn s hs)

end CycleState
end OddCycle
