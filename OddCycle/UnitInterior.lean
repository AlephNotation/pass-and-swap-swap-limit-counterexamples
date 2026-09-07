import OddCycle.UnitPlacementOrientation
import OddCycle.UnitOrientationBits

namespace OddCycle

def unitInterior (n w k : Nat) : Queue :=
  (CircularWord.realizingWord (unitOrientation w k)).filter
    (fun x => decide (2 * w + 2 ≤ x ∧ x < n - w))

theorem unitInterior_perm {n w k : Nat} (hw : 1 ≤ w) (hk : 2 ≤ k)
    (hn : n = 2 * k * w + 1) :
    (unitInterior n w k).Perm (List.range' (2 * w + 2) (n - (3 * w + 2))) := by
  have hsize : 3 * w + 2 ≤ n := by nlinarith [Nat.mul_le_mul_right w hk]
  have hp := CircularWord.realizingWord_perm (unitOrientation w k)
  have hlen : (unitOrientation w k).length = n := (unitOrientation_length (by omega)).trans hn.symm
  apply (List.perm_ext_iff_of_nodup ((hp.nodup_iff.mpr List.nodup_range).filter _) (List.nodup_range' ..)).mpr
  intro x
  simp only [List.mem_filter, hp.mem_iff, List.mem_range, hlen,
    decide_eq_true_eq, mem_range_interval]
  omega

theorem unitInterior_pairs {n w k i : Nat} (hw : 1 ≤ w) (hk : 2 ≤ k)
    (hn : n = 2 * k * w + 1) (hlo : 2 * w + 2 ≤ i) (hhi : i + 1 < n - w) :
    (if (unitOrientation w k)[i]'(by rw [unitOrientation_length (by omega)]; omega)
      then [i, i + 1] else [i + 1, i]).Sublist (unitInterior n w k) := by
  let q := CircularWord.realizingWord (unitOrientation w k)
  have hlen : (unitOrientation w k).length = n := (unitOrientation_length (by omega)).trans hn.symm
  have hp : q.Perm (List.range n) := by simpa only [hlen] using CircularWord.realizingWord_perm (unitOrientation w k)
  have hv : Valid n (q, []) := by simpa only [Valid, List.append_nil] using hp
  have ho : orientation n (q, []) = unitOrientation w k := by
    have hh := CircularWord.realizingWord_orientation (exceptional_encoding_nonconstant hw (by omega : 1 ≤ k) true)
    change orientation (unitOrientation w k).length (q, []) = unitOrientation w k at hh
    simpa only [hlen] using hh
  have hi : i < n := by omega
  have hj : i + 1 < n := by omega
  have hb : edgeBit n (q, []) i = (unitOrientation w k)[i] := by
    have hh := congrArg (fun l : List Bool => l[i]?) ho
    simpa only [List.getElem?_eq_getElem (l := orientation n (q, [])) (i := i) (by simpa only [orientation_length] using hi),
      List.getElem?_eq_getElem (by omega : i < (unitOrientation w k).length),
      Option.some.injEq, orientation_getElem hi] using hh
  have hqnd := hp.nodup_iff.mpr List.nodup_range
  have him : i ∈ q := hp.mem_iff.mpr (List.mem_range.mpr hi)
  have hjm : i + 1 ∈ q := hp.mem_iff.mpr (List.mem_range.mpr hj)
  have hmod : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt hj
  cases hbit : (unitOrientation w k)[i] with
  | true =>
    have hbefore : q.idxOf i < q.idxOf (i + 1) := by
      simpa only [hbit, edgeBit, placement, List.reverse_nil, List.append_nil, hmod, decide_eq_true_eq] using hb
    exact pair_sublist_filter _ (pair_sublist_of_before hqnd him hjm hbefore) (by simp; omega) (by simp; omega)
  | false =>
    have hbefore : q.idxOf (i + 1) < q.idxOf i := by
      have he := (edgeBit_false_iff (by omega) hi hv).mp (hb.trans hbit)
      simpa only [placement, List.reverse_nil, List.append_nil, hmod] using he
    exact pair_sublist_filter _ (pair_sublist_of_before hqnd hjm him hbefore) (by simp; omega) (by simp; omega)

theorem unit_target_orientation {n w k : Nat} (hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1) :
    orientation n (unitPatternTarget n w (unitInterior n w k).reverse) = unitOrientation w k := by
  apply unitPlacement_orientation hw (by nlinarith [Nat.mul_le_mul_right w hk]) (unitInterior_perm hw hk hn)
    ((unitOrientation_length (by omega)).trans hn.symm)
  · exact fun _ hi => unitOrientation_first hk hi
  · exact fun _ hlo hhi => unitOrientation_second hk hlo hhi
  · exact unitOrientation_left hw hk
  · exact unitOrientation_right hw hk hn
  · exact fun _ hlo hhi => unitOrientation_last hw hk hn hlo hhi
  · exact fun _ hlo hhi => unitInterior_pairs hw hk hn hlo hhi

end OddCycle
