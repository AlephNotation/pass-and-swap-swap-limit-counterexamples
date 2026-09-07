import OddCycle.OIGenerator

/-! Queue length is an autonomous birth--death observable for position-indexed
service rates, including OI allocations determined by prefix length. This is independent of the
swapping graph and replacement budget, and uses the original queue events. -/

noncomputable section

namespace OddCycle

theorem transition_first_length {adj : Nat → Nat → Bool} {budget pos init : Nat}
    {s t : State} {side : Bool} (h : transition adj budget s side pos = some (t, init)) :
    t.1.length = if side then s.1.length + 1 else s.1.length - 1 := by
  cases side with
  | false =>
    cases hc : complete adj budget s.1 pos with
    | none => simp [transition, hc] at h
    | some result =>
      obtain ⟨rest, departed, initiating⟩ := result
      simp [transition, hc] at h
      have hh := (complete_population hc).length_eq
      simp only [List.length_append, List.length_singleton] at hh
      have ht := congrArg (fun q : State => q.1.length) h.1
      change rest.length = t.1.length at ht
      simp only [Bool.false_eq_true, if_false]
      omega
  | true =>
    cases hc : complete adj budget s.2 pos with
    | none => simp [transition, hc] at h
    | some result =>
      obtain ⟨rest, departed, initiating⟩ := result
      simp [transition, hc] at h
      have ht := congrArg (fun q : State => q.1.length) h.1
      simpa only [List.length_append, List.length_singleton] using ht.symm

def lengthPositionDifference (adj : Nat → Nat → Bool) (budget : Nat) (s : State)
    (side : Bool) (p : Nat) (f : Nat → ℝ) : ℝ :=
  ((transition adj budget s side p).map (fun e => f e.1.1.length - f s.1.length)).getD 0

theorem lengthPositionDifference_eq (adj : Nat → Nat → Bool) (budget : Nat) (s : State)
    (side : Bool) (p : Nat) (hp : p < (if side then s.2 else s.1).length) (f : Nat → ℝ) :
    lengthPositionDifference adj budget s side p f =
      f (if side then s.1.length + 1 else s.1.length - 1) - f s.1.length := by
  obtain ⟨⟨t, init⟩, he⟩ := positions_are_events adj budget s ((mem_positions _ _ _).mpr hp)
  simp only [lengthPositionDifference, he, Option.map_some, Option.getD_some, transition_first_length he]

/-- Each zero-based occupied position receives its corresponding rate. -/
def lengthGenerator (adj : Nat → Nat → Bool) (budget : Nat) (a b : Nat → ℝ) (s : State) (f : Nat → ℝ) : ℝ :=
  ((List.range s.1.length).map (fun p => a p * lengthPositionDifference adj budget s false p f)).sum +
  ((List.range s.2.length).map (fun p => b p * lengthPositionDifference adj budget s true p f)).sum

theorem lengthGenerator_eq (adj : Nat → Nat → Bool) (budget : Nat) (a b : Nat → ℝ) (s : State) (f : Nat → ℝ) :
    lengthGenerator adj budget a b s f =
      ((List.range s.1.length).map a).sum * (f (s.1.length - 1) - f s.1.length) +
      ((List.range s.2.length).map b).sum * (f (s.1.length + 1) - f s.1.length) := by
  have hside (side : Bool) (rate : Nat → ℝ) :
      ((List.range (if side then s.2 else s.1).length).map
        (fun p => rate p * lengthPositionDifference adj budget s side p f)).sum =
      ((List.range (if side then s.2 else s.1).length).map rate).sum *
        (f (if side then s.1.length + 1 else s.1.length - 1) - f s.1.length) := by
    have hh : (List.range (if side then s.2 else s.1).length).map
        (fun p => rate p * lengthPositionDifference adj budget s side p f) =
        (List.range (if side then s.2 else s.1).length).map
        (fun p => rate p * (f (if side then s.1.length + 1 else s.1.length - 1) - f s.1.length)) := by
      apply List.map_congr_left
      intro p hp
      rw [lengthPositionDifference_eq adj budget s side p (List.mem_range.mp hp) f]
    rw [hh, List.sum_map_mul_right]
  exact congrArg₂ (· + ·) (hside false a) (hside true b)

theorem constant_lengthGenerator {n : Nat} {s : State} (hs : Valid n s)
    (adj : Nat → Nat → Bool) (budget : Nat) (a b : ℝ) (f : Nat → ℝ) :
    lengthGenerator adj budget (fun _ => a) (fun _ => b) s f =
      a * s.1.length * (f (s.1.length - 1) - f s.1.length) +
      b * (n - s.1.length) * (f (s.1.length + 1) - f s.1.length) := by
  have hl := hs.length_eq
  simp only [List.length_append, List.length_range] at hl
  rw [lengthGenerator_eq]
  simp only [List.map_const', List.length_range, List.sum_replicate, nsmul_eq_mul]
  rw [show s.2.length = n - s.1.length by omega, Nat.cast_sub (by omega : s.1.length ≤ n)]
  ring

theorem lengthGenerator_budget_independent (adj adj' : Nat → Nat → Bool) (w w' : Nat)
    (a b : Nat → ℝ) (s : State) (f : Nat → ℝ) :
    lengthGenerator adj w a b s f = lengthGenerator adj' w' a b s f := by
  rw [lengthGenerator_eq, lengthGenerator_eq]

def byLengthCapacity (μ : Nat → ℝ) (hμ : μ 0 = 0) : OICapacity ℝ where
  value q := μ q.length
  empty := hμ
  perm h := congrArg μ h.length_eq

theorem byLengthCapacity_increment (μ : Nat → ℝ) (hμ : μ 0 = 0) (q : Queue)
    (p : Nat) (hp : p < q.length) :
    (byLengthCapacity μ hμ).increment q p = μ (p + 1) - μ p := by
  change μ (q.take (p + 1)).length - μ (q.take p).length = _
  simp only [List.length_take, Nat.min_eq_left (by omega : p + 1 ≤ q.length),
    Nat.min_eq_left (by omega : p ≤ q.length)]

def positiveByLengthAllocation (n : Nat) (μ : Nat → ℝ) (hμ0 : μ 0 = 0)
    (hμ : ∀ p, p < n → 0 < μ (p + 1) - μ p) : PositiveOIAllocation n where
  toOICapacity := byLengthCapacity μ hμ0
  positive q hq p hp := by
    rw [byLengthCapacity_increment μ hμ0 q p hp]
    apply hμ
    have hl := hq.length_le
    simp only [List.length_range] at hl
    omega

theorem prefix_increment_sum (μ : Nat → ℝ) (k : Nat) :
    ((List.range k).map (fun p => μ (p + 1) - μ p)).sum = μ k - μ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp

theorem capacity_lengthGenerator {n : Nat} {s : State} (hs : Valid n s)
    (adj : Nat → Nat → Bool) (budget : Nat) (μ ν : Nat → ℝ)
    (hμ : μ 0 = 0) (hν : ν 0 = 0) (f : Nat → ℝ) :
    lengthGenerator adj budget (fun p => μ (p + 1) - μ p) (fun p => ν (p + 1) - ν p) s f =
      μ s.1.length * (f (s.1.length - 1) - f s.1.length) +
      ν (n - s.1.length) * (f (s.1.length + 1) - f s.1.length) := by
  have hl := hs.length_eq
  simp only [List.length_append, List.length_range] at hl
  rw [lengthGenerator_eq, prefix_increment_sum, prefix_increment_sum, hμ, hν, sub_zero, sub_zero,
    show s.2.length = n - s.1.length by omega]

end OddCycle
