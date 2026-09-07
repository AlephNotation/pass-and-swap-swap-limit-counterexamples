import OddCycle.UnlimitedPredecessors
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic

/-! Order-independent queue capacities and their canonical prefix weights.
The operational scan is unchanged; a position's rate is the increment of
capacity at that prefix. Positivity is required only on valid populations. -/

namespace OddCycle

variable {K : Type*} [Field K]

structure OICapacity (K : Type*) [Field K] where
  value : Queue → K
  empty : value [] = 0
  perm : ∀ {q r}, q.Perm r → value q = value r

namespace OICapacity

instance : CoeFun (OICapacity K) (fun _ => Queue → K) := ⟨value⟩

def prefixProduct (μ : OICapacity K) (pre : Queue) : Queue → K
  | [] => 1
  | x :: xs => (μ (pre ++ [x]))⁻¹ * μ.prefixProduct (pre ++ [x]) xs

def weight (μ : OICapacity K) (q : Queue) : K := μ.prefixProduct [] q

def increment (μ : OICapacity K) (q : Queue) (p : Nat) : K :=
  μ (q.take (p + 1)) - μ (q.take p)

def Regular (μ : OICapacity K) (q : Queue) : Prop :=
  ∀ r, r.Subperm q → r ≠ [] → μ r ≠ 0

theorem Regular.subperm {μ : OICapacity K} {q r : Queue} (h : μ.Regular q)
    (hr : r.Subperm q) : μ.Regular r := fun s hs hne => h s (hs.trans hr) hne

theorem Regular.perm {μ : OICapacity K} {q r : Queue} (h : μ.Regular q)
    (hr : q.Perm r) : μ.Regular r := h.subperm hr.symm.subperm

theorem prefixProduct_perm (μ : OICapacity K) {p q : Queue} (h : p.Perm q) (r : Queue) :
    μ.prefixProduct p r = μ.prefixProduct q r := by
  induction r generalizing p q with
  | nil => rfl
  | cons x xs ih =>
    simp only [prefixProduct, μ.perm (h.append_right [x]), ih (h.append_right [x])]

theorem prefixProduct_append (μ : OICapacity K) (pre q r : Queue) :
    μ.prefixProduct pre (q ++ r) = μ.prefixProduct pre q * μ.prefixProduct (pre ++ q) r := by
  induction q generalizing pre with
  | nil => simp [prefixProduct]
  | cons x xs ih => simp [prefixProduct, ih, List.append_assoc, mul_assoc]

theorem weight_append (μ : OICapacity K) (q r : Queue) :
    μ.weight (q ++ r) = μ.weight q * μ.prefixProduct q r := by
  simpa only [weight, List.nil_append] using μ.prefixProduct_append [] q r

theorem weight_append_singleton (μ : OICapacity K) (q : Queue) (x : Nat) :
    μ.weight (q ++ [x]) = μ.weight q * (μ (q ++ [x]))⁻¹ := by
  rw [μ.weight_append]
  simp only [prefixProduct, mul_one]

theorem weight_swap (μ : OICapacity K) (pre tail : Queue) (a b : Nat)
    (ha : μ (pre ++ [a]) ≠ 0) (hb : μ (pre ++ [b]) ≠ 0) :
    μ.weight (pre ++ a :: b :: tail) * μ (pre ++ [a]) =
      μ.weight (pre ++ b :: a :: tail) * μ (pre ++ [b]) := by
  have hp : (pre ++ [a] ++ [b]).Perm (pre ++ [b] ++ [a]) := by
    simpa only [List.append_assoc, List.singleton_append] using (List.Perm.swap b a []).append_left pre
  rw [μ.weight_append, μ.weight_append]
  simp only [prefixProduct]
  rw [μ.perm hp, μ.prefixProduct_perm hp]
  field_simp

theorem prefixProduct_ne_zero (μ : OICapacity K) {q : Queue} (hq : μ.Regular q)
    (pre tail : Queue) (hsub : (pre ++ tail).Subperm q) : μ.prefixProduct pre tail ≠ 0 := by
  induction tail generalizing pre with
  | nil => exact one_ne_zero
  | cons x xs ih =>
    rw [prefixProduct]
    apply mul_ne_zero
    · apply inv_ne_zero
      apply hq _ _ (by simp)
      exact ((List.prefix_append [x] xs).sublist.append_left pre).subperm.trans hsub
    · apply ih (pre ++ [x])
      simpa only [List.append_assoc, List.singleton_append] using hsub

theorem weight_ne_zero (μ : OICapacity K) {q : Queue} (hq : μ.Regular q) : μ.weight q ≠ 0 :=
  μ.prefixProduct_ne_zero hq [] q (by simpa only [List.nil_append] using List.Subperm.refl q)

end OICapacity

structure PositiveOIAllocation (n : Nat) extends OICapacity ℝ where
  positive : ∀ q, q.Subperm (List.range n) → ∀ p, p < q.length →
    0 < toOICapacity.increment q p

end OddCycle
