import OddCycle.GainedPredecessor
import OddCycle.ReverseCount

/-! Existence of the gained completion reconstructed from its exhausted
prefix; its unlimited continuation has a different departing job. -/

namespace OddCycle

def reconstructedGain (adj : Nat → Nat → Bool) (processed : Queue) (d : Nat) (tail : Queue) : Queue :=
  reverseInput adj processed d 0 ++ tail

theorem replacementCount_pos_of_neighbor {adj : Nat → Nat → Bool} {q : Queue} {job v : Nat}
    (hv : v ∈ q) (ha : adj job v = true) : 0 < replacementCount adj job q := by
  induction q with
  | nil => simp at hv
  | cons x xs ih =>
    by_cases hx : adj job x = true
    · simp [replacementCount, hx]
    · have hv' : v ∈ xs := by rcases List.mem_cons.mp hv with rfl | h; contradiction; exact h
      simpa [replacementCount, hx] using ih hv'

theorem reconstructedGain_complete {adj : Nat → Nat → Bool} (hsym : ∀ a b, adj a b = adj b a)
    (processed tail : Queue) (d w : Nat) (hc : replacementCount adj d processed.reverse = w) :
    complete adj w (reconstructedGain adj processed d tail) 0 =
      some (processed ++ tail, d, (unlimitedCarry adj d processed.reverse).2) := by
  let back := unlimitedCarry adj d processed.reverse
  have hi : unlimitedCarry adj back.2 back.1.reverse = (processed, d) := by
    simpa only [List.reverse_reverse] using unlimitedCarry_inverse hsym processed.reverse d
  have hcount : replacementCount adj back.2 back.1.reverse = w := (replacementCount_inverse hsym _ _).trans hc
  have hh := carry_append_of_count back.1.reverse tail w back.2 hcount.le
  rw [hcount, hi, Nat.sub_self, carry_zero] at hh
  change complete adj w (back.2 :: (back.1.reverse ++ tail)) 0 = some (processed ++ tail, d, back.2)
  simp only [complete, hh]

theorem reconstructedGain_changed {adj : Nat → Nat → Bool} (hsym : ∀ a b, adj a b = adj b a)
    (processed tail : Queue) (d big : Nat) (hnd : (d :: tail).Nodup)
    (hc : 0 < replacementCount adj d tail)
    (hbig : (reconstructedGain adj processed d tail).length ≤ big) :
    complete adj big (reconstructedGain adj processed d tail) 0 ≠
      some (processed ++ tail, d, (unlimitedCarry adj d processed.reverse).2) := by
  let back := unlimitedCarry adj d processed.reverse
  have hi : unlimitedCarry adj back.2 back.1.reverse = (processed, d) := by
    simpa only [List.reverse_reverse] using unlimitedCarry_inverse hsym processed.reverse d
  have hlen : (back.1.reverse ++ tail).length ≤ big := by
    simp only [reconstructedGain, reverseInput, List.take_zero, List.drop_zero, List.nil_append,
      List.length_append, List.length_cons] at hbig
    change back.1.reverse.length + 1 + tail.length ≤ big at hbig
    simp only [List.length_append]
    omega
  have hcar := carry_eq_unlimited adj (back.1.reverse ++ tail) back.2 big hlen
  rw [unlimitedCarry_append, hi] at hcar
  have hne := departed_ne_of_count_lt hnd hc
  rw [carry_zero] at hne
  intro he
  change complete adj big (back.2 :: (back.1.reverse ++ tail)) 0 = some (processed ++ tail, d, back.2) at he
  simp only [complete, hcar, Option.some.injEq, Prod.mk.injEq] at he
  exact hne he.2.1.symm

end OddCycle
