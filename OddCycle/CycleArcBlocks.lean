import OddCycle.CycleDirectedPaths
import OddCycle.CircularRunEncoding
import OddCycle.CycleRunStates

/-! Directed cycle arcs and homogeneous blocks of orientation bits. -/

namespace OddCycle

def edgeBit (n : Nat) (s : State) (i : Nat) : Bool :=
  decide ((placement s).idxOf i < (placement s).idxOf ((i + 1) % n))

theorem orientation_getElem {n i : Nat} {s : State} (hi : i < n) :
    (orientation n s)[i]'(by simpa only [orientation_length] using hi) = edgeBit n s i := by
  simp [orientation, edgeBit]

theorem edgeBit_false_iff {n i : Nat} {s : State} (hn : 2 ≤ n) (hi : i < n) (hs : Valid n s) :
    edgeBit n s i = false ↔ (placement s).idxOf ((i + 1) % n) < (placement s).idxOf i := by
  have hne : (i + 1) % n ≠ i := by
    intro hh
    have he := (clockwise_iff hi).mp hh
    omega
  have hm : i ∈ placement s := hs.placement_mem.mpr hi
  have hind : (placement s).idxOf i ≠ (placement s).idxOf ((i + 1) % n) := by
    intro hh
    exact hne ((List.idxOf_inj hm).mp hh).symm
  simp only [edgeBit, decide_eq_false_iff_not]
  omega

theorem sublist_iff_chain_before {p q : Queue} (hq : q.Nodup)
    (hm : ∀ x ∈ p, x ∈ q) :
    p.Sublist q ↔ p.IsChain (fun a b => q.idxOf a < q.idxOf b) := by
  constructor
  · intro hp
    have ho : q.Pairwise (fun a b => q.idxOf a < q.idxOf b) := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      simpa only [hq.idxOf_getElem i hi, hq.idxOf_getElem j hj] using hij
    exact (ho.sublist hp).isChain
  · intro hp
    letI : Trans (fun a b => q.idxOf a < q.idxOf b)
        (fun a b => q.idxOf a < q.idxOf b) (fun a b => q.idxOf a < q.idxOf b) := ⟨Nat.lt_trans⟩
    exact sublist_of_idxOf_pairwise hq hm hp.pairwise

theorem cycleArc_labels {n : Nat} (hn : 0 < n) (a length : Nat) :
    ∀ x ∈ cycleArc n a length, x < n := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact Nat.mod_lt _ hn

theorem cycleArc_forward_sublist_iff {n a length : Nat} {s : State}
    (hn : 0 < n) (hs : Valid n s) :
    (cycleArc n a length).Sublist (placement s) ↔
      ∀ i < length, edgeBit n s ((a + i) % n) = true := by
  rw [sublist_iff_chain_before hs.placement_nodup
    (fun x hx => hs.placement_mem.mpr (cycleArc_labels hn a length x hx)), List.isChain_iff_getElem]
  simp only [cycleArc, List.length_map, List.length_range, Nat.add_lt_add_iff_right,
    List.getElem_map, List.getElem_range, edgeBit, decide_eq_true_eq, Nat.mod_add_mod]
  congr! 3

theorem cycleArc_backward_sublist_iff {n a length : Nat} {s : State}
    (hn : 2 ≤ n) (hs : Valid n s) :
    (cycleArc n a length).reverse.Sublist (placement s) ↔
      ∀ i < length, edgeBit n s ((a + i) % n) = false := by
  rw [sublist_iff_chain_before hs.placement_nodup
    (fun x hx => hs.placement_mem.mpr
      (cycleArc_labels (by omega) a length x (by simpa using hx))), List.isChain_reverse,
    List.isChain_iff_getElem]
  simp only [cycleArc, List.length_map, List.length_range, Nat.add_lt_add_iff_right,
    List.getElem_map, List.getElem_range,
    edgeBit_false_iff hn (Nat.mod_lt _ (by omega)) hs, Nat.mod_add_mod]
  congr! 3

theorem orientation_rotate_getElem {n i : Nat} (s : State) (a : Nat) (hi : i < n) :
    ((orientation n s).rotate a)[i]'(by simpa only [List.length_rotate, orientation_length] using hi) =
      edgeBit n s ((a + i) % n) := by
  rw [List.getElem_rotate]
  simp [orientation, edgeBit, Nat.add_comm]

theorem orientation_prefix_eq {n length : Nat} {s : State} {b : Bool} (a : Nat)
    (hlen : length ≤ n) (hb : ∀ i < length, edgeBit n s ((a + i) % n) = b) :
    (orientation n s).rotate a = List.replicate length b ++ ((orientation n s).rotate a).drop length := by
  let q := (orientation n s).rotate a
  have hl : q.length = n := by simp only [q, List.length_rotate, orientation_length]
  have htake : q.take length = List.replicate length b := by
    apply List.ext_getElem
    · simp [hl, Nat.min_eq_left hlen]
    · intro i hi hj
      have hil : i < length := by simpa using hj
      have hin : i < n := hil.trans_le hlen
      simpa only [List.getElem_take, List.getElem_replicate, q,
        orientation_rotate_getElem s a hin] using hb i hil
  rw [← htake, List.take_append_drop]

theorem orientation_prefix_bits {n length : Nat} {s : State} {b : Bool} {tail : List Bool} (a : Nat)
    (he : (orientation n s).rotate a = List.replicate length b ++ tail) :
    length ≤ n ∧ ∀ i < length, edgeBit n s ((a + i) % n) = b := by
  have hl := congrArg List.length he
  simp only [List.length_rotate, orientation_length, List.length_append, List.length_replicate] at hl
  refine ⟨by omega, ?_⟩
  intro i hi
  have hin : i < n := by omega
  have hh := orientation_rotate_getElem s a hin
  have hp : ((orientation n s).rotate a)[i]'(by simpa only [List.length_rotate, orientation_length] using hin) = b := by
    simp [he, List.getElem_append_left, hi]
  exact hh.symm.trans hp

theorem orientation_circularBlock_iff {n length : Nat} {s : State} {b : Bool}
    (_hn : 0 < n) :
    CircularWord.CircularBlock (orientation n s) length b ↔
      length ≤ n ∧ ∃ a, ∀ i < length, edgeBit n s ((a + i) % n) = b := by
  constructor
  · rintro ⟨a, tail, he⟩
    have hh := orientation_prefix_bits a he
    exact ⟨hh.1, a, hh.2⟩
  · rintro ⟨hlen, a, hb⟩
    exact ⟨a, _, orientation_prefix_eq a hlen hb⟩

theorem circularBlock_iff_arc_sublist {n length : Nat} {s : State} {b : Bool}
    (hn : 2 ≤ n) (hs : Valid n s) :
    CircularWord.CircularBlock (orientation n s) length b ↔
      ∃ a, (if b then cycleArc n a length else (cycleArc n a length).reverse).Sublist (placement s) := by
  rw [orientation_circularBlock_iff (by omega)]
  have hlen {a : Nat}
      (h : (if b then cycleArc n a length else (cycleArc n a length).reverse).Sublist (placement s)) :
      length ≤ n := by
    have hh := h.length_le
    have hp := hs.placement_perm.length_eq
    cases b <;> simp [cycleArc] at hh hp <;> omega
  constructor
  · rintro ⟨_, a, hb⟩
    refine ⟨a, ?_⟩
    cases b with
    | false => exact (cycleArc_backward_sublist_iff hn hs).mpr hb
    | true => exact (cycleArc_forward_sublist_iff (by omega) hs).mpr hb
  · rintro ⟨a, ha⟩
    refine ⟨hlen ha, a, ?_⟩
    cases b with
    | false => exact (cycleArc_backward_sublist_iff hn hs).mp ha
    | true => exact (cycleArc_forward_sublist_iff (by omega) hs).mp ha

theorem cycleArc_path (n a length : Nat) : pathEdges (cycleAdjacent n) (cycleArc n a length) = true := by
  rw [pathEdges_iff_isChain, List.isChain_iff_getElem]
  intro i hi
  apply (cycleAdjacent_clockwise_iff _ _ _).mpr
  apply Or.inl
  simp [cycleArc, Clockwise, Nat.mod_add_mod, Nat.add_assoc]

/-- The original directed-path height agrees exactly with the maximum
circular run length, expressed without introducing a second height definition. -/
theorem shortRuns_iff_height {n w : Nat} {s : State} (hn : 2 ≤ n) (hs : Valid n s) :
    ShortRuns n w s ↔ height n s ≤ w := by
  change CircularRun.Short w (CircularWord.circularRuns (orientation n s)) ↔ _
  rw [CircularWord.short_iff_no_long_circularBlock (orientation_nonconstant hn hs)]
  constructor
  · intro h
    apply pathsBounded_iff_height.mp
    intro p hp he
    by_cases hnil : p = []
    · simp [hnil]
    · obtain ⟨a, _, ha⟩ := cycle_path_is_arc hnil (hs.placement_nodup.sublist hp)
        (fun x hx => hs.placement_mem.mp (hp.subset hx)) he
      have hbound : p.length - 1 ≤ w := by
        rcases ha with ha | ha
        · apply h (p.length - 1) true
          apply (circularBlock_iff_arc_sublist hn hs).mpr
          exact ⟨a, by simpa [← ha] using hp⟩
        · apply h (p.length - 1) false
          apply (circularBlock_iff_arc_sublist hn hs).mpr
          exact ⟨a, by simpa [← ha] using hp⟩
      omega
  · intro hh length b hb
    obtain ⟨a, ha⟩ := (circularBlock_iff_arc_sublist hn hs).mp hb
    have hpath : pathEdges (cycleAdjacent n)
        (if b then cycleArc n a length else (cycleArc n a length).reverse) = true := by
      cases b with
      | true => exact cycleArc_path n a length
      | false => exact (pathEdges_reverse (cycleAdjacent_symm n) _).mpr (cycleArc_path n a length)
    have hl := (pathsBounded_iff_height.mpr hh) _ ha hpath
    cases b <;> simp [cycleArc] at hl <;> omega

theorem shortRuns_reachable_iff {n w : Nat} {s t : State} (hn : 2 ≤ n)
    (hs : Valid n s) (ht : Valid n t) (hshort : ShortRuns n w s) :
    EventReachable (cycleAdjacent n) w s t ↔ orientation n s = orientation n t :=
  short_reachable_iff (by omega) hs ht ((shortRuns_iff_height hn hs).mp hshort)

theorem shortRuns_terminal {n w : Nat} (hn : 2 ≤ n) (s : CycleState n)
    (hs : ShortRuns n w s.val) : ReachabilityQuotient.Terminal (CycleState.Step n w) s :=
  short_terminal (by omega) s ((shortRuns_iff_height hn s.property).mp hs)

end OddCycle
