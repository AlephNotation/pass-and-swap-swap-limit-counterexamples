import OddCycle.UnitLengthKernel
import OddCycle.KernelRestriction

/-! The actual unit-rate kernel restricted to a closed cycle class and its
proved queue-length projection. -/

noncomputable section

namespace OddCycle

abbrev ClassState (states : List State) := ↥states.toFinset

namespace ClosedClass

variable {n w : Nat} {states : List State} (hc : ClosedClass n w states)

def embedding : ClassState states ↪ CycleState n where
  toFun s := ⟨s.val, hc.valid s.val (List.mem_toFinset.mp s.property)⟩
  inj' _ _ h := Subtype.ext (congrArg (fun t : CycleState n => t.val) h)

theorem embedding_val (s : ClassState states) : (hc.embedding s).val = s.val := rfl

theorem kernel_closed (hn : 0 < n) (s : ClassState states) (t : CycleState n)
    (h : 0 < ((unitPositions n).kernel hn w).prob (hc.embedding s) t) :
    ∃ u, hc.embedding u = t := by
  have ht := hc.closed s.val (List.mem_toFinset.mp s.property) t.val
    (((unitPositions n).kernel_pos_iff hn w _ _).mp h)
  exact ⟨⟨t.val, List.mem_toFinset.mpr ht⟩, Subtype.ext rfl⟩

def unitKernel (hn : 0 < n) : FiniteMarkov (ClassState states) :=
  ((unitPositions n).kernel hn w).restrictEmbedding hc.embedding (hc.kernel_closed hn)

theorem unitKernel_embedding (hn : 0 < n) :
    (hc.unitKernel hn).LumpsTo ((unitPositions n).kernel hn w) hc.embedding :=
  FiniteMarkov.restrictEmbedding_lumps _ _ _

theorem unitKernel_step (hn : 0 < n) (s t : ClassState states)
    (h : EventStep (cycleAdjacent n) w s.val t.val) : 0 < (hc.unitKernel hn).prob s t :=
  ((unitPositions n).kernel_pos_iff hn w (hc.embedding s) (hc.embedding t)).mpr h

theorem unitKernel_irreducible (hn : 0 < n) : (hc.unitKernel hn).Irreducible := by
  intro s t
  have hr := hc.communicate s.val (List.mem_toFinset.mp s.property) t.val (List.mem_toFinset.mp t.property)
  have liftPath : ∀ {u : State}, EventReachable (cycleAdjacent n) w s.val u →
      ∀ hu : u ∈ states.toFinset, (hc.unitKernel hn).Reachable s ⟨u, hu⟩ := by
    intro u path
    induction path with
    | refl => intro _; exact .refl
    | @tail u v path step ih =>
      intro hv
      have hu := List.mem_toFinset.mpr (hc.reachable (List.mem_toFinset.mp s.property) path)
      exact (ih hu).tail (hc.unitKernel_step hn ⟨u, hu⟩ ⟨v, hv⟩ step)
  exact liftPath hr t.property

def queueLength (s : ClassState states) : Fin (n + 1) := (hc.wordCutEquiv s).2

theorem queueLength_val (s : ClassState states) : (hc.queueLength s).val = s.val.1.length := rfl

theorem queueLength_surjective : Function.Surjective hc.queueLength := by
  intro k
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil states hc.nonempty
  let q : ↥(states.toFinset.image placement) :=
    ⟨placement s, Finset.mem_image.mpr ⟨s, List.mem_toFinset.mpr hs, rfl⟩⟩
  obtain ⟨t, ht⟩ := hc.wordCutEquiv.surjective (q, k)
  exact ⟨t, congrArg Prod.snd ht⟩

def lengthRepresentative : Fin (n + 1) → ClassState states := Function.surjInv hc.queueLength_surjective

theorem lengthRepresentative_length (k : Fin (n + 1)) :
    hc.queueLength (hc.lengthRepresentative k) = k :=
  Function.rightInverse_surjInv hc.queueLength_surjective k

def lengthKernel (hn : 0 < n) : FiniteMarkov (Fin (n + 1)) :=
  (hc.unitKernel hn).project hc.queueLength hc.lengthRepresentative

theorem unitKernel_generator (hn : 0 < n) (s : ClassState states) (f : Nat → ℝ) :
    (n : ℝ) * ((hc.unitKernel hn).expect (fun t => f t.val.1.length) s - f s.val.1.length) =
      lengthGenerator (cycleAdjacent n) w (fun _ => 1) (fun _ => 1) s.val f := by
  have he := (hc.unitKernel_embedding hn).expect (fun t => f t.val.1.length) s
  have hh := unitKernel_length_generator hn w (hc.embedding s) f
  change (hc.unitKernel hn).expect (fun t => f t.val.1.length) s = _ at he
  rw [he]
  exact hh

theorem unitKernel_lumps (hn : 0 < n) : (hc.unitKernel hn).LumpsTo (hc.lengthKernel hn) hc.queueLength := by
  apply FiniteMarkov.lumps_project _ _ _ hc.lengthRepresentative_length
  intro s t hst
  funext j
  let f : Nat → ℝ := fun k => if k = j.val then 1 else 0
  have hs := hc.unitKernel_generator hn s f
  have ht := hc.unitKernel_generator hn t f
  have hlen : s.val.1.length = t.val.1.length := congrArg Fin.val hst
  rw [constant_lengthGenerator (hc.valid _ (List.mem_toFinset.mp s.property))] at hs
  rw [constant_lengthGenerator (hc.valid _ (List.mem_toFinset.mp t.property))] at ht
  rw [hlen] at hs
  have he : (hc.unitKernel hn).expect (fun u => f u.val.1.length) s =
      (hc.unitKernel hn).expect (fun u => f u.val.1.length) t := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith
  simpa only [FiniteMarkov.push, FiniteMarkov.expect, f, ← queueLength_val hc, Fin.val_inj,
    mul_ite, mul_one, mul_zero] using he

theorem lengthKernel_irreducible (hn : 0 < n) : (hc.lengthKernel hn).Irreducible :=
  (hc.unitKernel_lumps hn).irreducible (hc.unitKernel_irreducible hn) hc.queueLength_surjective

end ClosedClass
end OddCycle
