import OddCycle.ShortOIStationary

/-! Explicit orientation-class supports and the canonical law on each class. -/

namespace OddCycle

theorem allStates_nodup (n : Nat) : (allStates n).Nodup := by
  unfold allStates
  apply List.nodup_flatMap.mpr
  constructor
  · intro q hq
    have hlen := (List.mem_permutations'.mp hq).length_eq
    simp only [List.length_range] at hlen
    apply List.nodup_range.map_on
    intro a ha b hb he
    have ha' : a ≤ q.length := by have := List.mem_range.mp ha; omega
    have hb' : b ≤ q.length := by have := List.mem_range.mp hb; omega
    have hh := congrArg (fun s : State => s.1.length) he
    simpa only [List.length_take, Nat.min_eq_left ha', Nat.min_eq_left hb'] using hh
  · have hnd := (List.permutations_perm_permutations' (List.range n)).nodup_iff.mp
      (List.nodup_permutations _ List.nodup_range)
    apply hnd.imp
    intro a b hab s hsa hsb
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hsa
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hsb
    have he := congrArg (fun s : State => s.1 ++ s.2) (hi.trans hj.symm)
    simp only [List.take_append_drop] at he
    exact hab he

def orientationStates (n : Nat) (o : List Bool) : List State :=
  (allStates n).filter (fun s => orientation n s == o)

theorem mem_orientationStates {n : Nat} {o : List Bool} {s : State} :
    s ∈ orientationStates n o ↔ Valid n s ∧ orientation n s = o := by
  simp [orientationStates, mem_allStates_iff]

theorem orientationStates_support (n : Nat) (o : List Bool) :
    OrientationSupport n (orientationStates n o) where
  nodup := (allStates_nodup n).filter _
  valid _ hs := (mem_orientationStates.mp hs).1
  fiber _ hs _ ht ho := mem_orientationStates.mpr ⟨ht, ho.trans (mem_orientationStates.mp hs).2⟩

theorem orientationStates_short {n w : Nat} {s : State} (hs : Valid n s) (hw : height n s ≤ w) :
    ∀ t ∈ orientationStates n (orientation n s), height n t ≤ w := by
  intro t ht
  obtain ⟨ht, ho⟩ := mem_orientationStates.mp ht
  rwa [height_eq_of_orientation_eq ht hs ho]

theorem orientation_class_oi_stationary {n w : Nat} (hn : 0 < n)
    (μ ν : PositiveOIAllocation n) {s : State} (hs : Valid n s) (hw : height n s ≤ w) :
    OIStationary (cycleAdjacent n) w μ.toOICapacity ν.toOICapacity
      (orientationStates n (orientation n s)) (oiCanonicalWeight μ.toOICapacity ν.toOICapacity) :=
  positive_short_oi_stationary hn (orientationStates_support n (orientation n s))
    (orientationStates_short hs hw) μ ν

theorem nonexceptional_recurrent_oi_stationary {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w)
    (hlength : ¬ ∃ k, 1 ≤ k ∧ n = 2 * k * w + 1)
    (μ ν : PositiveOIAllocation n) (s : CycleState n)
    (ht : ReachabilityQuotient.Terminal (CycleState.Step n w) s) :
    OIStationary (cycleAdjacent n) w μ.toOICapacity ν.toOICapacity
      (orientationStates n (orientation n s.val)) (oiCanonicalWeight μ.toOICapacity ν.toOICapacity) := by
  exact orientation_class_oi_stationary (by omega) μ ν s.property
    ((shortRuns_iff_height (by omega) s.property).mp
      (CycleState.terminal_short_of_nonexceptional_length hn hw hlength s ht))

theorem even_recurrent_oi_stationary {n w : Nat} (hn : 3 ≤ n) (hw : 1 ≤ w) (heven : Even n)
    (μ ν : PositiveOIAllocation n) (s : CycleState n)
    (ht : ReachabilityQuotient.Terminal (CycleState.Step n w) s) :
    OIStationary (cycleAdjacent n) w μ.toOICapacity ν.toOICapacity
      (orientationStates n (orientation n s.val)) (oiCanonicalWeight μ.toOICapacity ν.toOICapacity) := by
  exact orientation_class_oi_stationary (by omega) μ ν s.property
    ((shortRuns_iff_height (by omega) s.property).mp (CycleState.even_terminal_short hn hw heven s ht))

end OddCycle
