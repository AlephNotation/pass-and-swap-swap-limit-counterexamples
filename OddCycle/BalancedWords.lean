import OddCycle.BranchChains

/-! A repetition-free enumeration of exactly the balanced placement words. -/

namespace OddCycle

def frameWords (w source : Nat) (forward : Bool) : List Queue :=
  (interleavings (longInterior w source forward) (shortInterior w source forward)).map
    (fun mid => source :: mid ++ [cycleLabel (2 * w + 1) source forward (w + 1)])

theorem interiors_nodup {w source : Nat} (hw : 2 ≤ w) (hs : source < 2 * w + 1)
    (forward : Bool) : (longInterior w source forward ++ shortInterior w source forward).Nodup := by
  have hc := (branchState_valid hw hs forward).placement_nodup
  simp only [placement, branchState, List.reverse_nil, List.append_nil, branchWord_eq_interiors] at hc
  exact (List.nodup_append.mp (List.nodup_cons.mp hc).2).1

theorem frameWords_length (w source : Nat) (forward : Bool) :
    (frameWords w source forward).length = Nat.choose (w + (w - 1)) w := by
  simp [frameWords, interleavings_length, longInterior, shortInterior]

theorem frameWords_nodup {w source : Nat} (hw : 2 ≤ w) (hs : source < 2 * w + 1)
    (forward : Bool) : (frameWords w source forward).Nodup := by
  apply (interleavings_nodup (interiors_nodup hw hs forward)).map
  intro a b hab
  simpa using hab

theorem frameWord_valid {w source : Nat} (hw : 2 ≤ w) (hs : source < 2 * w + 1)
    (forward : Bool) {q : Queue} (hq : q ∈ frameWords w source forward) :
    Valid (2 * w + 1) (q, []) := by
  obtain ⟨mid, hm, rfl⟩ := List.mem_map.mp hq
  have hp := ((mem_interleavings_iff (interiors_nodup hw hs forward)).mp hm).1
  have hc := branchState_valid hw hs forward
  simp only [Valid, branchState, List.append_nil, branchWord_eq_interiors] at hc ⊢
  exact ((hp.cons source).append (List.Perm.refl _)).trans hc

theorem frameWord_orientation {w source : Nat} (hw : 2 ≤ w) (hs : source < 2 * w + 1)
    (forward : Bool) {q : Queue} (hq : q ∈ frameWords w source forward) :
    orientation (2 * w + 1) (q, []) = orientation (2 * w + 1) (branchState w source forward) := by
  have hv := frameWord_valid hw hs forward hq
  obtain ⟨mid, hm, rfl⟩ := List.mem_map.mp hq
  exact orientation_of_placement_interleaving hw hs hv forward hm (by simp [placement])

theorem mem_frameWords_iff {w source : Nat} (hw : 2 ≤ w) (hs : source < 2 * w + 1)
    (forward : Bool) (q : Queue) : q ∈ frameWords w source forward ↔
      Valid (2 * w + 1) (q, []) ∧
        orientation (2 * w + 1) (q, []) = orientation (2 * w + 1) (branchState w source forward) := by
  constructor
  · intro hq
    exact ⟨frameWord_valid hw hs forward hq, frameWord_orientation hw hs forward hq⟩
  · rintro ⟨hv, hori⟩
    obtain ⟨mid, hm, heq⟩ := placement_interleaving_of_orientation hw hs hv forward hori
    exact List.mem_map.mpr ⟨mid, hm, by simpa [placement] using heq.symm⟩

theorem frameWords_source_sink {w source : Nat} {forward : Bool} {q : Queue}
    (hq : q ∈ frameWords w source forward) :
    q.head? = some source ∧ q.getLast? = some (cycleLabel (2 * w + 1) source forward (w + 1)) := by
  obtain ⟨mid, _, rfl⟩ := List.mem_map.mp hq
  constructor
  · rfl
  · rw [List.getLast?_append]
    rfl

theorem frameWords_unique {w a b : Nat} (hw : 2 ≤ w) (ha : a < 2 * w + 1)
    {f g : Bool} {q : Queue} (hq : q ∈ frameWords w a f) (hq' : q ∈ frameWords w b g) :
    a = b ∧ f = g := by
  obtain ⟨has, hat⟩ := frameWords_source_sink hq
  obtain ⟨hbs, hbt⟩ := frameWords_source_sink hq'
  have heq : a = b := Option.some.inj (has.symm.trans hbs)
  subst b
  refine ⟨rfl, ?_⟩
  have he : cycleLabel (2 * w + 1) a f (w + 1) = cycleLabel (2 * w + 1) a g (w + 1) :=
    Option.some.inj (hat.symm.trans hbt)
  by_contra hfg
  have hg : g = !f := by cases f <;> cases g <;> simp_all
  rw [hg, cycleLabel_not (by omega) f] at he
  have hr : reflect (2 * w + 1) (w + 1) = w := by
    rw [reflect_eq (by omega), if_neg (by omega)]
    omega
  rw [hr] at he
  have := cycleLabel_injective ha (show w + 1 < 2 * w + 1 by omega) (show w < 2 * w + 1 by omega) f he
  omega

def balancedWords (w : Nat) : List Queue :=
  (List.range (2 * w + 1)).flatMap (fun source =>
    [true, false].flatMap (frameWords w source))

theorem balancedWords_length (w : Nat) :
    (balancedWords w).length = 2 * (2 * w + 1) * Nat.choose (w + (w - 1)) w := by
  simp [balancedWords, List.length_flatMap, frameWords_length, List.sum_replicate]
  ring

theorem balancedWords_nodup {w : Nat} (hw : 2 ≤ w) : (balancedWords w).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro source hsource
    have hs := List.mem_range.mp hsource
    apply List.nodup_flatMap.mpr
    constructor
    · intro forward _
      exact frameWords_nodup hw hs forward
    · rw [List.pairwise_pair]
      intro q hq hq'
      have := (frameWords_unique hw hs hq hq').2
      contradiction
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij q hq hq'
    simp only [List.length_range] at hi hj
    simp only [List.getElem_range, List.mem_flatMap] at hq hq'
    obtain ⟨f, _, hf⟩ := hq
    obtain ⟨g, _, hg⟩ := hq'
    have := (frameWords_unique hw hi hf hg).1
    omega

theorem mem_balancedWords_iff {w : Nat} (hw : 2 ≤ w) (q : Queue) :
    q ∈ balancedWords w ↔ Valid (2 * w + 1) (q, []) ∧ balanced w (q, []) = true := by
  simp only [balancedWords, List.mem_flatMap, balanced, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨source, hs, f, hf, hq⟩
    obtain ⟨hv, ho⟩ := (mem_frameWords_iff hw (List.mem_range.mp hs) f q).mp hq
    exact ⟨hv, source, hs, f, hf, ho⟩
  · rintro ⟨hv, source, hs, f, hf, ho⟩
    exact ⟨source, hs, f, hf, (mem_frameWords_iff hw (List.mem_range.mp hs) f q).mpr ⟨hv, ho⟩⟩

end OddCycle
