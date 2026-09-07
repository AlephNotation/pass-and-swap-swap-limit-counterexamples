import OddCycle.ExceptionalCycleCommunication

namespace OddCycle

def unitOrientation (w k : Nat) : List Bool := CircularWord.encode true (exceptionalRunList w k)

theorem unitOrientation_length {w k : Nat} (hk : 1 ≤ k) : (unitOrientation w k).length = 2 * k * w + 1 := by
  simp only [unitOrientation, CircularWord.encode_length, exceptionalRunList_sum hk]

theorem unitOrientation_start {w k : Nat} (hk : 2 ≤ k) :
    unitOrientation w k = List.replicate (w + 1) true ++
      (List.replicate w false ++ (List.replicate w true ++ CircularWord.encode false (List.replicate (2 * k - 3) w))) := by
  unfold unitOrientation exceptionalRunList
  rw [show 2 * k - 1 = (2 * k - 3 + 1) + 1 by omega, List.replicate_succ, List.replicate_succ]
  simp [CircularWord.encode]

theorem unitOrientation_finish {w k : Nat} (hk : 2 ≤ k) :
    ∃ pre, pre.length + 2 * w = 2 * k * w + 1 ∧
      unitOrientation w k = pre ++ (List.replicate w true ++ List.replicate w false) := by
  let r := (w + 1) :: List.replicate (2 * k - 3) w
  have hr : exceptionalRunList w k = r ++ [w, w] := by
    unfold exceptionalRunList r
    simp only [List.cons_append]
    rw [show 2 * k - 1 = (2 * k - 3) + 2 by omega, List.replicate_add]
    rfl
  have heven : r.length % 2 = 0 := by
    simp only [r, List.length_cons, List.length_replicate]
    omega
  have he : unitOrientation w k = CircularWord.encode true r ++ (List.replicate w true ++ List.replicate w false) := by
    rw [unitOrientation, hr, CircularWord.encode_append]
    simp [CircularWord.phase, heven, CircularWord.encode]
  refine ⟨CircularWord.encode true r, ?_, he⟩
  have hh := congrArg List.length he
  rw [unitOrientation_length (by omega)] at hh
  simp only [List.length_append, List.length_replicate] at hh
  omega

theorem getElem_constant_block {q pre post : List Bool} {len i : Nat} {b : Bool}
    (he : q = pre ++ (List.replicate len b ++ post)) (hi : i < q.length)
    (hlo : pre.length ≤ i) (hhi : i < pre.length + len) : q[i] = b := by
  subst q
  rw [List.getElem_append_right hlo]
  rw [List.getElem_append_left (by simp; omega)]
  simp

theorem unitOrientation_first {w k i : Nat} (hk : 2 ≤ k) (hi : i ≤ w) :
    (unitOrientation w k)[i]'(by rw [unitOrientation_length (by omega)]; nlinarith [Nat.mul_le_mul_right w hk]) = true := by
  apply getElem_constant_block (pre := []) (len := w + 1)
    (by simpa using unitOrientation_start (w := w) hk) _ (by simp) (by simp; omega)

theorem unitOrientation_second {w k i : Nat} (hk : 2 ≤ k) (hlo : w + 1 ≤ i) (hhi : i ≤ 2 * w) :
    (unitOrientation w k)[i]'(by rw [unitOrientation_length (by omega)]; nlinarith [Nat.mul_le_mul_right w hk]) = false := by
  apply getElem_constant_block (pre := List.replicate (w + 1) true) (len := w)
    (unitOrientation_start hk) _ (by simpa) (by simp; omega)

theorem unitOrientation_left {w k : Nat} (hw : 1 ≤ w) (hk : 2 ≤ k) :
    (unitOrientation w k)[2 * w + 1]'(by rw [unitOrientation_length (by omega)]; nlinarith) = true := by
  have he := unitOrientation_start (w := w) hk
  apply getElem_constant_block (pre := List.replicate (w + 1) true ++ List.replicate w false) (len := w)
    (by simpa only [List.append_assoc] using he) _ (by simp; omega) (by simp; omega)

theorem unitOrientation_last {n w k i : Nat} (_hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1)
    (hlo : n - w ≤ i) (hhi : i < n) :
    (unitOrientation w k)[i]'(by rw [unitOrientation_length (by omega)]; omega) = false := by
  obtain ⟨pre, hlen, he⟩ := unitOrientation_finish (w := w) hk
  apply getElem_constant_block (pre := pre ++ List.replicate w true) (post := []) (len := w)
    (by simpa only [List.append_assoc, List.append_nil] using he) _ (by simp; omega) (by simp; omega)

theorem unitOrientation_right {n w k : Nat} (hw : 1 ≤ w) (hk : 2 ≤ k) (hn : n = 2 * k * w + 1) :
    (unitOrientation w k)[n - w - 1]'(by rw [unitOrientation_length (by omega)]; omega) = true := by
  obtain ⟨pre, hlen, he⟩ := unitOrientation_finish (w := w) hk
  apply getElem_constant_block (pre := pre) (len := w) he _ (by omega) (by omega)

end OddCycle
