import OddCycle.OINormalization

/-! Additive class rates, including identical unit rates, are positive OI
allocations. Their new prefix weights equal the existing canonical weights. -/

namespace OddCycle

variable {K : Type*} [Field K]

def additiveCapacity (rate : Nat → K) : OICapacity K where
  value q := (q.map rate).sum
  empty := rfl
  perm hp := (hp.map rate).sum_eq

theorem additive_increment (rate : Nat → K) (q : Queue) (p : Nat) (hp : p < q.length) :
    (additiveCapacity rate).increment q p = rate q[p] := by
  change ((q.take (p + 1)).map rate).sum - ((q.take p).map rate).sum = rate q[p]
  rw [List.take_succ_eq_append_getElem hp]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, add_sub_cancel_left]

theorem additive_prefixProduct (rate : Nat → K) (pre q : Queue) :
    (additiveCapacity rate).prefixProduct pre q = prefixWeight rate ((pre.map rate).sum) q := by
  induction q generalizing pre with
  | nil => rfl
  | cons a q ih =>
    simp only [OICapacity.prefixProduct, ih, prefixWeight]
    simp [additiveCapacity]

theorem additive_weight (rate : Nat → K) (q : Queue) :
    (additiveCapacity rate).weight q = prefixWeight rate 0 q := by
  simpa only [OICapacity.weight, List.map_nil, List.sum_nil] using additive_prefixProduct rate [] q

theorem additive_canonicalWeight (rate : Nat → K) (s : State) :
    oiCanonicalWeight (additiveCapacity rate) (additiveCapacity rate) s = canonicalWeight rate s := by
  simp only [oiCanonicalWeight, additive_weight, canonicalWeight]

noncomputable def positiveAdditiveAllocation (n : Nat) (rate : Nat → ℝ) (hr : ∀ x, x < n → 0 < rate x) :
    PositiveOIAllocation n where
  toOICapacity := additiveCapacity rate
  positive q hq p hp := by
    rw [additive_increment rate q p hp]
    exact hr q[p] (List.mem_range.mp (hq.subset (List.getElem_mem hp)))

noncomputable def unitAllocation (n : Nat) : PositiveOIAllocation n :=
  positiveAdditiveAllocation n (fun _ => 1) (by intros; exact zero_lt_one)

theorem unit_capacity {n : Nat} (q : Queue) : (unitAllocation n).value q = (q.length : ℝ) := by
  simp [unitAllocation, positiveAdditiveAllocation, additiveCapacity]

theorem unit_increment {n : Nat} (q : Queue) (p : Nat) (hp : p < q.length) :
    (unitAllocation n).toOICapacity.increment q p = 1 := additive_increment _ q p hp

theorem unit_weight {n : Nat} (q : Queue) :
    (unitAllocation n).toOICapacity.weight q = (q.length.factorial : ℝ)⁻¹ := by
  induction q using List.reverseRecOn with
  | nil => simp [OICapacity.weight, OICapacity.prefixProduct]
  | append_singleton q a ih =>
    rw [OICapacity.weight_append_singleton, ih, unit_capacity]
    simp only [List.length_append, List.length_singleton, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev]

theorem unit_canonicalWeight {n : Nat} (s : State) :
    oiCanonicalWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity s =
      (s.1.length.factorial : ℝ)⁻¹ * (s.2.length.factorial : ℝ)⁻¹ := by
  simp only [oiCanonicalWeight, unit_weight]

theorem unit_fullQueue_weight {n : Nat} {q : Queue} (hq : q.length = n) :
    oiCanonicalWeight (unitAllocation n).toOICapacity (unitAllocation n).toOICapacity ([], q) =
      (n.factorial : ℝ)⁻¹ := by
  simp [unit_canonicalWeight, hq]

end OddCycle
