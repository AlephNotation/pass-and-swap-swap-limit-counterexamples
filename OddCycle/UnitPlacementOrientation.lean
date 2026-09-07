import OddCycle.UnitPlacement

namespace OddCycle

theorem unitPlacement_orientation {n w : Nat} (hw : 1 ≤ w) (hn : 3 * w + 2 ≤ n)
    {H : Queue} (hH : H.Perm (List.range' (2 * w + 2) (n - (3 * w + 2))))
    {bits : List Bool} (hlen : bits.length = n)
    (hfirst : ∀ i (hi : i ≤ w), bits[i]'(by omega) = true)
    (hsecond : ∀ i (hlo : w + 1 ≤ i) (hhi : i ≤ 2 * w), bits[i]'(by omega) = false)
    (hleft : bits[2 * w + 1]'(by omega) = true)
    (hright : bits[n - w - 1]'(by omega) = true)
    (hlast : ∀ i (_hlo : n - w ≤ i) (hhi : i < n), bits[i]'(by omega) = false)
    (hinner : ∀ i (hlo : 2 * w + 2 ≤ i) (hhi : i + 1 < n - w),
      (if bits[i]'(by omega) then [i, i + 1] else [i + 1, i]).Sublist H) :
    orientation n (unitPatternTarget n w H.reverse) = bits := by
  apply orientation_eq_of_edge_pairs (unitPatternTarget_valid hn hH) hlen
  intro i hi
  rw [unitPatternTarget_placement]
  let F := List.range' 0 (w + 1)
  let B := (List.range' (w + 1) (w + 1)).reverse
  let A := (unitInitialBlock n w).reverse
  have hF : F.Sublist (unitPlacement n w H) := List.sublist_append_left _ _
  have hB : B.Sublist (unitPlacement n w H) :=
    (List.sublist_append_left B (H ++ A)).trans (List.sublist_append_right F (B ++ (H ++ A)))
  have hHsub : H.Sublist (unitPlacement n w H) :=
    (List.sublist_append_left H A).trans ((List.sublist_append_right B (H ++ A)).trans
      (List.sublist_append_right F (B ++ (H ++ A))))
  have hA : A.Sublist (unitPlacement n w H) :=
    (List.sublist_append_right H A).trans ((List.sublist_append_right B (H ++ A)).trans
      (List.sublist_append_right F (B ++ (H ++ A))))
  have memF (a : Nat) (ha : a ≤ w) : a ∈ F := mem_range_interval.mpr ⟨by omega, by omega⟩
  have memB (a : Nat) (ha : w + 1 ≤ a) (hb : a ≤ 2 * w + 1) : a ∈ B :=
    List.mem_reverse.mpr (mem_range_interval.mpr ⟨ha, by omega⟩)
  have memA (a : Nat) (ha : n - w ≤ a) (hb : a < n) : a ∈ A :=
    List.mem_reverse.mpr (mem_range_interval.mpr ⟨ha, by omega⟩)
  have crossFB {a b : Nat} (ha : a ∈ F) (hb : b ∈ B) : [a, b].Sublist (unitPlacement n w H) := by
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using pair_across_blocks [] F [] B (H ++ A) ha hb
  have crossBH {a b : Nat} (ha : a ∈ B) (hb : b ∈ H) : [a, b].Sublist (unitPlacement n w H) := by
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using pair_across_blocks F B [] H A ha hb
  have crossBA {a b : Nat} (ha : a ∈ B) (hb : b ∈ A) : [a, b].Sublist (unitPlacement n w H) := by
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using pair_across_blocks F B H A [] ha hb
  have crossHA {a b : Nat} (ha : a ∈ H) (hb : b ∈ A) : [a, b].Sublist (unitPlacement n w H) := by
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using pair_across_blocks (F ++ B) H [] A [] ha hb
  have crossFA {a b : Nat} (ha : a ∈ F) (hb : b ∈ A) : [a, b].Sublist (unitPlacement n w H) := by
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using pair_across_blocks [] F (B ++ H) A [] ha hb
  by_cases hend : i + 1 = n
  · have hiend : i = n - 1 := by omega
    rw [hlast i (by omega) hi, hend, Nat.mod_self]
    exact crossFA (memF 0 (by omega)) (memA i (by omega) hi)
  have hnext : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt (by omega)
  rw [hnext]
  by_cases hifirst : i ≤ w
  · rw [hfirst i hifirst]
    by_cases hilast : i = w
    · subst i
      exact crossFB (memF w le_rfl) (memB (w + 1) le_rfl (by omega))
    · exact (pair_sublist_range (start := 0) (count := w + 1) (by omega) (by omega)).trans hF
  by_cases hisecond : i ≤ 2 * w
  · rw [hsecond i (by omega) hisecond]
    exact (pair_sublist_reverse_range (start := w + 1) (count := w + 1) (by omega) (by omega)).trans hB
  by_cases hileft : i = 2 * w + 1
  · subst i
    rw [hleft]
    by_cases hmiddle : 2 * w + 2 < n - w
    · exact crossBH (memB _ (by omega) le_rfl)
        ((unitPlacement_middle_mem hn hH _).mpr ⟨by omega, by omega⟩)
    · exact crossBA (memB _ (by omega) le_rfl) (memA _ (by omega) (by omega))
  by_cases hitail : n - w ≤ i
  · rw [hlast i hitail hi]
    exact (pair_sublist_reverse_range (start := n - w) (count := w) hitail (by omega)).trans hA
  by_cases hiright : i + 1 = n - w
  · have he : i = n - w - 1 := by omega
    have hb : bits[i] = true := by simpa only [he] using hright
    rw [hb]
    exact crossHA ((unitPlacement_middle_mem hn hH i).mpr ⟨by omega, by omega⟩)
      (memA (i + 1) (by omega) (by omega))
  exact (hinner i (by omega) (by omega)).trans hHsub

end OddCycle
