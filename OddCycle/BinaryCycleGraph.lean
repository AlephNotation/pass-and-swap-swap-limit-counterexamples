import OddCycle.CircularBitDynamics
import OddCycle.FiniteGraphSymmetry
import Mathlib.Data.Fintype.Pi

/-! The finite graph of nonconstant circular binary words. Circular changes
of cut and global complementation are graph automorphisms, so the auxiliary
augmentation used for run extraction preserves terminal membership. -/

namespace OddCycle.CircularWord

theorem rotate_cancel (q : List Bool) (k : Nat) :
    (q.rotate k).rotate (q.length - k % q.length) = q := by
  have h := List.rotate_eq_iff.mp (rfl : q.rotate k = q.rotate k)
  simpa only [List.length_rotate] using h.symm

theorem CircularFlip.rotate_iff {w k : Nat} {q z : List Bool} (hlen : q.length = z.length) :
    CircularFlip w (q.rotate k) (z.rotate k) ↔ CircularFlip w q z := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨k + i, by simpa only [List.rotate_rotate] using hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨q.length - k % q.length + i, ?_⟩
    rw [← List.rotate_rotate, ← List.rotate_rotate, rotate_cancel,
      hlen, rotate_cancel]
    exact hi

theorem LinearFlip.not {w : Nat} {q z : List Bool} (h : LinearFlip w q z) :
    LinearFlip w (q.map Bool.not) (z.map Bool.not) := by
  cases h with
  | first pre post b =>
    simpa only [List.map_append, List.map_replicate, List.map_cons] using
      LinearFlip.first (pre.map Bool.not) (post.map Bool.not) (!b)
  | last pre post b =>
    simpa only [List.map_append, List.map_replicate, List.map_cons] using
      LinearFlip.last (pre.map Bool.not) (post.map Bool.not) (!b)

theorem CircularFlip.not {w : Nat} {q z : List Bool} (h : CircularFlip w q z) :
    CircularFlip w (q.map Bool.not) (z.map Bool.not) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by simpa only [List.map_rotate] using hk.not⟩

theorem CircularFlip.not_iff {w : Nat} {q z : List Bool} :
    CircularFlip w (q.map Bool.not) (z.map Bool.not) ↔ CircularFlip w q z := by
  constructor
  · intro h
    simpa [List.map_map, Function.comp_def] using h.not
  · exact CircularFlip.not

theorem Nonconstant.not {q : List Bool} (hq : Nonconstant q) : Nonconstant (q.map Bool.not) := by
  obtain ⟨a, ha, b, hb, hne⟩ := hq
  exact ⟨!a, List.mem_map.mpr ⟨a, ha, rfl⟩, !b, List.mem_map.mpr ⟨b, hb, rfl⟩, by simpa using hne⟩

theorem AugmentedStep.length_eq {w : Nat} {q z : List Bool} (h : AugmentedStep w q z) :
    q.length = z.length := by
  cases h with
  | flip hf => exact hf.length_eq
  | rotate hr => exact hr.perm.length_eq
  | negate => simp

theorem CircularFlip.augmentedReach {w : Nat} {q z : List Bool} (h : CircularFlip w q z) :
    AugmentedReach w q z := by
  obtain ⟨k, hk⟩ := h
  exact (Relation.ReflTransGen.single (AugmentedStep.rotate ⟨k, rfl⟩)).trans
    ((Relation.ReflTransGen.single (AugmentedStep.flip hk)).trans
      (Relation.ReflTransGen.single (AugmentedStep.rotate (List.IsRotated.forall z k))))

end OddCycle.CircularWord

namespace OddCycle

abbrev BinaryCycle (n : Nat) := {q : List Bool // q.length = n ∧ CircularWord.Nonconstant q}

namespace BinaryCycle

noncomputable instance (n : Nat) : Fintype (BinaryCycle n) := by
  let f : BinaryCycle n → (Fin n → Bool) :=
    fun q i => q.val[i.val]'(by simpa only [q.property.1] using i.isLt)
  apply Fintype.ofInjective f
  intro q z he
  apply Subtype.ext
  apply List.ext_getElem
  · exact q.property.1.trans z.property.1.symm
  · intro i hi hj
    have hin : i < n := by simpa only [q.property.1] using hi
    exact congrFun he ⟨i, hin⟩

def Step (n w : Nat) (q z : BinaryCycle n) : Prop := CircularWord.CircularFlip w q.val z.val

def Symmetry (n : Nat) (q z : BinaryCycle n) : Prop :=
  List.IsRotated q.val z.val ∨ z.val = q.val.map Bool.not

def rotated {n : Nat} (k : Nat) (q : BinaryCycle n) : BinaryCycle n :=
  ⟨q.val.rotate k, by simpa using q.property.1, q.property.2.perm (List.rotate_perm q.val k).symm⟩

def negated {n : Nat} (q : BinaryCycle n) : BinaryCycle n :=
  ⟨q.val.map Bool.not, by simpa using q.property.1, q.property.2.not⟩

def rotateEquiv (n k : Nat) : BinaryCycle n ≃ BinaryCycle n where
  toFun := rotated k
  invFun := rotated (n - k % n)
  left_inv q := by
    apply Subtype.ext
    change (q.val.rotate k).rotate (n - k % n) = q.val
    simpa only [q.property.1] using CircularWord.rotate_cancel q.val k
  right_inv q := by
    apply Subtype.ext
    change (q.val.rotate (n - k % n)).rotate k = q.val
    rw [List.rotate_rotate, Nat.add_comm, ← List.rotate_rotate]
    simpa only [q.property.1] using CircularWord.rotate_cancel q.val k

def negateEquiv (n : Nat) : BinaryCycle n ≃ BinaryCycle n where
  toFun := negated
  invFun := negated
  left_inv q := by apply Subtype.ext; simp [negated, List.map_map, Function.comp_def]
  right_inv q := by apply Subtype.ext; simp [negated, List.map_map, Function.comp_def]

theorem rotate_preserves (n w k : Nat) :
    ReachabilityQuotient.Preserves (Step n w) (rotateEquiv n k) := by
  intro q z
  exact CircularWord.CircularFlip.rotate_iff (q.property.1.trans z.property.1.symm)

theorem negate_preserves (n w : Nat) :
    ReachabilityQuotient.Preserves (Step n w) (negateEquiv n) := by
  intro q z
  exact CircularWord.CircularFlip.not_iff

theorem symmetry_symm {n : Nat} (q z : BinaryCycle n) (h : Symmetry n q z) : Symmetry n z q := by
  rcases h with h | h
  · exact Or.inl h.symm
  · apply Or.inr
    have hh := congrArg (List.map Bool.not) h
    simpa [List.map_map, Function.comp_def] using hh.symm

theorem symmetry_automorphism (n w : Nat) (q z : BinaryCycle n) (h : Symmetry n q z) :
    ∃ e : BinaryCycle n ≃ BinaryCycle n, ReachabilityQuotient.Preserves (Step n w) e ∧ e q = z := by
  rcases h with ⟨k, hk⟩ | h
  · exact ⟨rotateEquiv n k, rotate_preserves n w k, Subtype.ext hk⟩
  · exact ⟨negateEquiv n, negate_preserves n w, Subtype.ext h.symm⟩

abbrev Augmented (n w : Nat) := ReachabilityQuotient.Augment (Step n w) (Symmetry n)

theorem augmented_terminal_iff (n w : Nat) (q : BinaryCycle n) :
    ReachabilityQuotient.Terminal (Augmented n w) q ↔ ReachabilityQuotient.Terminal (Step n w) q :=
  ReachabilityQuotient.terminal_augment_iff (Step n w) (Symmetry n) symmetry_symm
    (symmetry_automorphism n w) q

theorem augmented_reach_projects {n w : Nat} {q z : BinaryCycle n}
    (h : Relation.ReflTransGen (Augmented n w) q z) :
    CircularWord.AugmentedReach w q.val z.val := by
  apply Relation.ReflTransGen.lift' Subtype.val ?_ h
  intro a b hab
  rcases hab with hab | hab | hab
  · exact hab.augmentedReach
  · exact .single (.rotate hab)
  · rw [hab]
    exact .single (.negate _)

theorem augmented_reach_lifts {n w : Nat} (hw : 1 ≤ w) {q : BinaryCycle n} {z : List Bool}
    (h : CircularWord.AugmentedReach w q.val z) :
    ∃ hz : z.length = n ∧ CircularWord.Nonconstant z,
      Relation.ReflTransGen (Augmented n w) q ⟨z, hz⟩ := by
  induction h with
  | refl => exact ⟨q.property, .refl⟩
  | @tail a b _ hab ih =>
    obtain ⟨ha, hqa⟩ := ih
    have hb : b.length = n ∧ CircularWord.Nonconstant b :=
      ⟨hab.length_eq.symm.trans ha.1, hab.nonconstant hw ha.2⟩
    refine ⟨hb, hqa.tail ?_⟩
    cases hab with
    | flip hf => exact Or.inl ⟨0, by simpa using hf⟩
    | rotate hr => exact Or.inr (Or.inl hr)
    | negate => exact Or.inr (Or.inr rfl)

theorem terminal_iff_word_terminal {n w : Nat} (hw : 1 ≤ w) (q : BinaryCycle n) :
    ReachabilityQuotient.Terminal (Augmented n w) q ↔
      ReachabilityQuotient.Terminal (CircularWord.AugmentedStep w) q.val := by
  constructor
  · intro ht z hz
    obtain ⟨hv, hqz⟩ := augmented_reach_lifts hw hz
    exact augmented_reach_projects (ht ⟨z, hv⟩ hqz)
  · intro ht z hz
    have hr := ht z.val (augmented_reach_projects hz)
    obtain ⟨hv, hreturn⟩ := augmented_reach_lifts hw hr
    exact hreturn

/-- Exact terminal-state classification for the unaugmented circular bit
flip graph. Rotations and complementation are absent from `Step`. -/
theorem terminal_iff {n w : Nat} (hw : 1 ≤ w) (q : BinaryCycle n) :
    ReachabilityQuotient.Terminal (Step n w) q ↔
      CircularRun.Short w (CircularWord.circularRuns q.val) ∨
        CircularRun.Exceptional w (CircularWord.circularRuns q.val) := by
  rw [← augmented_terminal_iff, terminal_iff_word_terminal hw,
    CircularWord.augmented_terminal_iff hw q.property.2]

end BinaryCycle
end OddCycle
