import OddCycle.FrontierInversion
import OddCycle.UnlimitedPredecessors

/-! Uniqueness of the gained predecessor from the two neighbor positions
in the target queue. This argument is independent of the intervening jobs. -/

namespace OddCycle

theorem idxOf_middle (pre tail : Queue) (a : Nat) (hnd : (pre ++ a :: tail).Nodup) :
    (pre ++ a :: tail).idxOf a = pre.length := by
  have hn : a ∉ pre := by
    intro ha
    exact (List.nodup_append.mp hnd).2.2 a ha a (by simp) rfl
  simp [List.idxOf_append, hn]

theorem idxOf_last_add_one {q : Queue} {a : Nat} (hnd : q.Nodup) (ha : q.getLast? = some a) :
    q.idxOf a + 1 = q.length := by
  obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp ha
  have hh := idxOf_middle pre [] a hnd
  simpa using hh

theorem changed_predecessor_unique {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) {rest q : Queue} {w big pos init d a b : Nat}
    (hw : 0 < w) (hbig : q.length ≤ big) (hnd : rest.Nodup)
    (hneighbors : ∀ v ∈ rest, adj v d = true → v = a ∨ v = b)
    (ha : rest.idxOf a + 1 = w) (hb : rest.getLast? = some b)
    (he : complete adj w q pos = some (rest, d, init))
    (hne : complete adj big q pos ≠ some (rest, d, init)) :
    pos = 0 ∧ q = reverseInput adj (rest.take w) d 0 ++ rest.drop w := by
  obtain ⟨pre, processed, untouched, previous, hr, hp, ht, hwlen, hlast, hadj, hq⟩ :=
    changed_complete_reconstruct hsym hw hbig he hne
  have hidx : rest.idxOf previous + 1 = pre.length + processed.length := by
    obtain ⟨p, hproc⟩ := List.getLast?_eq_some_iff.mp hlast
    have hr' : rest = (pre ++ p) ++ previous :: untouched := by
      simp only [hr, hproc, List.append_assoc, List.singleton_append]
    have hh := idxOf_middle (pre ++ p) untouched previous (by simpa only [← hr'] using hnd)
    rw [hr']
    rw [hh]
    simp [hproc, Nat.add_assoc]
  have hlt : pre.length + processed.length < rest.length := by
    have htlen := List.length_pos_iff.mpr ht
    simp only [hr, List.length_append]
    omega
  have hpa : previous = a := by
    have hm : previous ∈ rest := by
      obtain ⟨p, hproc⟩ := List.getLast?_eq_some_iff.mp hlast
      simp [hr, hproc]
    rcases hneighbors previous hm hadj with h | h
    · exact h
    · have hh := idxOf_last_add_one hnd hb
      rw [h] at hidx
      omega
  rw [hpa, ha] at hidx
  have hpre : pre = [] := by
    apply List.length_eq_zero_iff.mp
    omega
  have hproc : processed.length = w := by simp only [hpre, List.length_nil, Nat.zero_add] at hidx; omega
  have hr' : rest = processed ++ untouched := by simpa only [hpre, List.nil_append] using hr
  have htake : rest.take w = processed := by rw [hr', ← hproc]; simp
  have hdrop : rest.drop w = untouched := by rw [hr', ← hproc]; simp
  refine ⟨by simpa only [hpre, List.length_nil] using hp.symm, ?_⟩
  rw [htake, hdrop]
  simpa only [hpre, List.nil_append, reverseInput, List.take_zero, List.drop_zero] using hq

end OddCycle
