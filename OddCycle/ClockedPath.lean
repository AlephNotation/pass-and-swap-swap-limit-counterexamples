import OddCycle.ExponentialClocks
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Nonexplosive continuous-time paths obtained by putting exponential clocks
between the states of a finite jump chain. Every clock in the probability
space satisfies the required pathwise properties. -/

namespace OddCycle.ClockedPath

open Filter Finset
open scoped Topology NNReal

variable {S : Type*} [Fintype S]
variable (rate : S → ℝ) (positive : ∀ s, 0 < rate s)
variable (y : Nat → S) (z : ExponentialClock.Clock)

noncomputable def arrival (n : Nat) : ℝ := ∑ i ∈ Finset.range n, z.val i / rate (y i)

omit [Fintype S] in
@[simp] theorem arrival_zero : arrival rate y z 0 = 0 := by simp [arrival]

omit [Fintype S] in
theorem arrival_succ (n : Nat) : arrival rate y z (n + 1) = arrival rate y z n + z.val n / rate (y n) := by
  exact Finset.sum_range_succ _ _

include positive

omit [Fintype S] in
theorem arrival_strictMono : StrictMono (arrival rate y z) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [arrival_succ]
  exact lt_add_of_pos_right _ (div_pos (ExponentialClock.clock_positive z n) (positive _))

omit [Fintype S] in
theorem arrival_nonneg (n : Nat) : 0 ≤ arrival rate y z n := by
  simpa only [arrival_zero] using (arrival_strictMono rate positive y z).monotone (Nat.zero_le n)

theorem arrival_diverges : Tendsto (arrival rate y z) atTop atTop := by
  classical
  let C := (∑ s, rate s) + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun s _ => (positive s).le)) zero_lt_one
  have hbound (s : S) : rate s ≤ C := by
    have hh := Finset.single_le_sum (fun s _ => (positive s).le) (Finset.mem_univ s)
    dsimp only [C]
    linarith
  have hsum (n : Nat) : (∑ i ∈ Finset.range n, z.val i) ≤ C * arrival rate y z n := by
    rw [arrival, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have he := mul_le_mul_of_nonneg_right (hbound (y i)) (div_pos (ExponentialClock.clock_positive z i) (positive (y i))).le
    have hi : rate (y i) * (z.val i / rate (y i)) = z.val i := by field_simp [(positive (y i)).ne']
    rwa [hi] at he
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(ExponentialClock.clock_diverges z).eventually_ge_atTop (C * b)] with n hn
  have hh := hsum n
  nlinarith

theorem exists_next (t : ℝ) : ∃ n, t < arrival rate y z (n + 1) := by
  obtain ⟨n, hn⟩ := ((arrival_diverges rate positive y z).eventually_gt_atTop t).exists
  exact ⟨n, hn.trans ((arrival_strictMono rate positive y z) (Nat.lt_succ_self n))⟩

noncomputable def index (t : ℝ≥0) : Nat := Nat.find (exists_next rate positive y z t)

theorem index_upper (t : ℝ≥0) : (t : ℝ) < arrival rate y z (index rate positive y z t + 1) :=
  Nat.find_spec (exists_next rate positive y z t)

theorem index_lower (t : ℝ≥0) : arrival rate y z (index rate positive y z t) ≤ t := by
  cases hi : index rate positive y z t with
  | zero => simpa only [arrival_zero] using t.property
  | succ n =>
    have hn : n < index rate positive y z t := by omega
    exact le_of_not_gt (Nat.find_min (exists_next rate positive y z t) hn)

theorem index_at_arrival (n : Nat) :
    index rate positive y z ⟨arrival rate y z n, arrival_nonneg rate positive y z n⟩ = n := by
  let t : ℝ≥0 := ⟨arrival rate y z n, arrival_nonneg rate positive y z n⟩
  change index rate positive y z t = n
  have hlow := index_lower rate positive y z t
  have hupp := index_upper rate positive y z t
  have hm := arrival_strictMono rate positive y z
  apply Nat.le_antisymm
  · exact hm.le_iff_le.mp hlow
  · have hlt := hm.lt_iff_lt.mp hupp
    omega

noncomputable def state (t : ℝ≥0) : S := y (index rate positive y z t)

theorem index_eq_iff (t : ℝ≥0) (n : Nat) :
    index rate positive y z t = n ↔ arrival rate y z n ≤ t ∧ t < arrival rate y z (n + 1) := by
  constructor
  · intro h
    subst n
    exact ⟨index_lower rate positive y z t, index_upper rate positive y z t⟩
  · rintro ⟨hl, hu⟩
    have hm := arrival_strictMono rate positive y z
    have h₁ := hm.lt_iff_lt.mp ((index_lower rate positive y z t).trans_lt hu)
    have h₂ := hm.lt_iff_lt.mp (hl.trans_lt (index_upper rate positive y z t))
    omega

theorem state_between (t : ℝ≥0) (n : Nat)
    (hl : arrival rate y z n ≤ t) (hu : t < arrival rate y z (n + 1)) :
    state rate positive y z t = y n := by
  rw [state, (index_eq_iff rate positive y z t n).mpr ⟨hl, hu⟩]

theorem state_at_arrival (n : Nat) :
    state rate positive y z ⟨arrival rate y z n, arrival_nonneg rate positive y z n⟩ = y n := by
  rw [state, index_at_arrival]

theorem visits_iff (A : S → Prop) : (∃ t, A (state rate positive y z t)) ↔ ∃ n, A (y n) := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨index rate positive y z t, ht⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨arrival rate y z n, arrival_nonneg rate positive y z n⟩, by simpa only [state_at_arrival] using hn⟩

theorem returns_iff (s : S) :
    (∃ t : ℝ≥0, arrival rate y z 1 ≤ t ∧ state rate positive y z t = s) ↔
      ∃ n, 1 ≤ n ∧ y n = s := by
  constructor
  · rintro ⟨t, ht, hs⟩
    refine ⟨index rate positive y z t, ?_, hs⟩
    by_contra hh
    have hz : index rate positive y z t = 0 := by omega
    have hu := index_upper rate positive y z t
    rw [hz] at hu
    linarith
  · rintro ⟨n, hn, hs⟩
    exact ⟨⟨arrival rate y z n, arrival_nonneg rate positive y z n⟩,
      (arrival_strictMono rate positive y z).monotone hn, by simpa only [state_at_arrival] using hs⟩

end OddCycle.ClockedPath
