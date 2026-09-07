import OddCycle.ExceptionalCycleCommunication
import Mathlib.Algebra.BigOperators.Fin

/-! A first-moment argument distinguishes all rotations of an odd binary
word whose two bit counts differ by one. This supplies injectivity of the
exceptional-orientation parameters without enumerating words. -/

namespace OddCycle.CircularWord

open scoped BigOperators

def cyclicBit {n : Nat} [NeZero n] (q : List Bool) (hlen : q.length = n) (i : ZMod n) : Bool :=
  q[i.val]'(by simpa only [hlen] using i.val_lt)

theorem finEquiv_val {n : Nat} [NeZero n] (i : Fin n) : (ZMod.finEquiv n i).val = i.val := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => rfl

theorem sum_cyclicBit {n : Nat} [NeZero n] {K : Type*} [AddCommMonoid K]
    (q : List Bool) (hlen : q.length = n) (v : Bool → K) :
    (∑ i : ZMod n, v (cyclicBit q hlen i)) = (q.map v).sum := by
  have hlist : List.ofFn (fun i : Fin n => cyclicBit q hlen (ZMod.finEquiv n i)) = q := by
    apply List.ext_getElem
    · simpa using hlen.symm
    · intro i hi hj
      simp only [List.getElem_ofFn, cyclicBit, finEquiv_val]
  calc
    _ = ∑ i : Fin n, v (cyclicBit q hlen (ZMod.finEquiv n i)) :=
      ((ZMod.finEquiv n).toEquiv.sum_comp (fun i => v (cyclicBit q hlen i))).symm
    _ = (List.ofFn (fun i : Fin n => v (cyclicBit q hlen (ZMod.finEquiv n i)))).sum :=
      List.sum_ofFn.symm
    _ = (q.map v).sum := by
      change (List.ofFn (v ∘ (fun i : Fin n => cyclicBit q hlen (ZMod.finEquiv n i)))).sum = _
      rw [← List.map_ofFn, hlist]

theorem sum_true_indicator {K : Type*} [Semiring K] (q : List Bool) :
    (q.map (fun b => if b then (1 : K) else 0)).sum = (q.count true : K) := by
  induction q with
  | nil => simp
  | cons b q ih => cases b <;> simp [ih, add_comm]

def bitMass {n : Nat} [NeZero n] (f : ZMod n → Bool) : ZMod n := ∑ i, if f i then 1 else 0
def bitMoment {n : Nat} [NeZero n] (f : ZMod n → Bool) : ZMod n := ∑ i, if f i then i else 0

theorem cyclicBit_mass {n : Nat} [NeZero n] (q : List Bool) (hlen : q.length = n) :
    bitMass (cyclicBit q hlen) = (q.count true : ZMod n) := by
  unfold bitMass
  exact (sum_cyclicBit q hlen (fun b => if b then (1 : ZMod n) else 0)).trans (sum_true_indicator q)

theorem bitMoment_shift {n : Nat} [NeZero n] (f : ZMod n → Bool) (a : ZMod n) :
    bitMoment (fun i => f (i + a)) = bitMoment f - a * bitMass f := by
  have hterm (i : ZMod n) : (if f (i + a) then i else 0) =
      (if f (i + a) then i + a else 0) - a * (if f (i + a) then 1 else 0) := by
    split_ifs <;> ring
  unfold bitMoment bitMass
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hm := Equiv.sum_comp (Equiv.addRight a) (fun i : ZMod n => if f i then i else 0)
  have hc := Equiv.sum_comp (Equiv.addRight a) (fun i : ZMod n => if f i then (1 : ZMod n) else 0)
  simpa only [Equiv.coe_addRight] using congrArg₂ (fun x y => x - a * y) hm hc

theorem shift_injective_of_half_mass {n : Nat} [NeZero n] {f : ZMod n → Bool}
    (hmass : 2 * bitMass f = 1 ∨ 2 * bitMass f = -1) {a b : ZMod n}
    (h : ∀ i, f (i + a) = f (i + b)) : a = b := by
  have he : (fun i => f (i + a)) = (fun i => f (i + b)) := funext h
  have hm := congrArg bitMoment he
  rw [bitMoment_shift, bitMoment_shift] at hm
  have hp : a * bitMass f = b * bitMass f := by
    have hh := congrArg (fun x => bitMoment f - x) hm
    simpa using hh
  have hz : (a - b) * bitMass f = 0 := by rw [sub_mul, hp, sub_self]
  have hz' : (a - b) * (2 * bitMass f) = 0 := by
    calc
      _ = 2 * ((a - b) * bitMass f) := by ring
      _ = 0 := by rw [hz, mul_zero]
  rcases hmass with hm | hm
  · rw [hm, mul_one] at hz'
    exact sub_eq_zero.mp hz'
  · rw [hm, mul_neg_one] at hz'
    exact sub_eq_zero.mp (neg_eq_zero.mp hz')

theorem cyclicBit_rotate {n : Nat} [NeZero n] (q : List Bool) (hlen : q.length = n) (a i : ZMod n) :
    cyclicBit (q.rotate a.val) (by simpa using hlen) i = cyclicBit q hlen (i + a) := by
  simp only [cyclicBit, List.getElem_rotate, hlen, ZMod.val_add]

end OddCycle.CircularWord
