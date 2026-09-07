import OddCycle.Certificate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Finite, kernel-checked results for C₅, replacement budget 2, and class rates
(2,1,1,1,1). The certificate supplies candidate weights and paths only;
all transitions, orientations, and canonical weights come from Model.lean.
-/

namespace OddCycle.FiveJob

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def adj := cycleAdjacent 5
def rate (job : Nat) : ℚ := if job = 0 then 2 else 1
def support : List State := witnesses.map Witness.state
def root : State := ([0, 1], [2, 3, 4])
def target : State := ([0], [2, 1, 3, 4])

def integerWeight (s : State) : Nat :=
  ((witnesses.find? (fun row => row.state == s)).map Witness.weight).getD 0

def weight (s : State) : ℚ := integerWeight s

theorem support_size : support.length = 180 := by decide +kernel
theorem support_nodup : support.Nodup := by decide +kernel
theorem support_valid : ∀ s ∈ support, Valid 5 s := by decide +kernel
theorem support_balanced : ∀ s ∈ support, balanced 2 s = true := by decide +kernel

/-- Exhaustiveness is checked against all 720 states, not only certificate rows. -/
theorem support_exhaustive :
    ∀ s ∈ allStates 5, (s ∈ support ↔ balanced 2 s = true) := by decide +kernel

theorem mem_support_iff {s : State} :
    s ∈ support ↔ Valid 5 s ∧ balanced 2 s = true := by
  constructor
  · intro hs
    exact ⟨support_valid s hs, support_balanced s hs⟩
  · rintro ⟨hv, hb⟩
    exact (support_exhaustive s (mem_allStates_iff.mpr hv)).mpr hb

theorem support_height : ∀ s ∈ support, height 5 s = 3 := by decide +kernel

/-- Closure includes every occupied position in both queues. -/
theorem support_closed :
    ∀ s ∈ support, ∀ e ∈ events adj 2 s, e.1 ∈ support := by decide +kernel

def followHeads : State → List Bool → Option State
  | s, [] => some s
  | s, side :: rest => do
    let e ← transition adj 2 s side 0
    followHeads e.1 rest

def HeadStep (s t : State) : Prop :=
  ∃ side job, transition adj 2 s side 0 = some (t, job)

abbrev HeadReachable := Relation.ReflTransGen HeadStep

theorem followHeads_reachable {path : List Bool} {s t : State}
    (h : followHeads s path = some t) : HeadReachable s t := by
  induction path generalizing s with
  | nil =>
    simp only [followHeads, Option.some.injEq] at h
    subst t
    exact Relation.ReflTransGen.refl
  | cons side rest ih =>
    cases he : transition adj 2 s side 0 with
    | none => simp [followHeads, he] at h
    | some e =>
      have hr : followHeads e.1 rest = some t := by simpa [followHeads, he] using h
      exact (Relation.ReflTransGen.single ⟨side, e.2, he⟩).trans (ih hr)

theorem head_paths_checked :
    ∀ row ∈ witnesses,
      followHeads root row.fromRoot = some row.state ∧
      followHeads row.state row.toRoot = some root := by decide +kernel

/-- Communication uses only head completions, so it needs no non-head rates. -/
theorem head_communication {s t : State} (hs : s ∈ support) (ht : t ∈ support) :
    HeadReachable s t := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  exact (followHeads_reachable (head_paths_checked a ha).2).trans
    (followHeads_reachable (head_paths_checked b hb).1)

theorem target_mem : target ∈ support := by decide +kernel

/-- Direct balance from all events in the closed region; no two-flow lemma
or imported unlimited-product-form theorem is assumed. -/
theorem canonical_defect :
    balance adj 2 rate support (canonicalWeight rate) target = -(1 / 360 : ℚ) := by
  decide +kernel

theorem canonical_not_stationary :
    ¬ Stationary adj 2 rate support (canonicalWeight rate) := by
  intro h
  have hz := h target target_mem
  rw [canonical_defect] at hz
  norm_num at hz

theorem certificate_positive : ∀ s ∈ support, 0 < integerWeight s := by decide +kernel

theorem certificate_total :
    (support.map integerWeight).sum = 29781619500363599243784 := by decide +kernel

theorem certificate_stationary : Stationary adj 2 rate support weight := by
  -- Each equation gets its own auxiliary theorem, so the kernel can release
  -- its reduction cache before checking the next equation.
  simp only [Stationary, support, witnesses, List.map_cons, List.map_nil,
    List.forall_mem_cons]
  repeat' constructor
  all_goals as_aux_lemma => decide +kernel

def c₁ : Queue := [0, 1]
def c₂ : Queue := [1, 0]
def d₁ : Queue := [3, 2, 4]
def d₂ : Queue := [3, 4, 2]

theorem rectangle_mem :
    (c₁, d₁) ∈ support ∧ (c₁, d₂) ∈ support ∧
    (c₂, d₁) ∈ support ∧ (c₂, d₂) ∈ support := by decide +kernel

theorem rectangle_values :
    integerWeight (c₁, d₁) = 177097849418281817550 ∧
    integerWeight (c₁, d₂) = 177080689708261370580 ∧
    integerWeight (c₂, d₁) = 506774969345262400380 ∧
    integerWeight (c₂, d₂) = 507080673408934957320 := by decide +kernel

/-- The obstruction applies to factors in any characteristic-zero field,
including real-valued factors; the weights are embedded using Nat.cast. -/
theorem certificate_not_product {R : Type*} [Field R] [CharZero R] :
    ¬ ∃ (K : R) (A B : Queue → R),
      ∀ s ∈ support, (integerWeight s : R) = K * A s.1 * B s.2 := by
  rintro ⟨K, A, B, h⟩
  obtain ⟨hm11, hm12, hm21, hm22⟩ := rectangle_mem
  have hz : (integerWeight (c₁, d₁) : R) * integerWeight (c₂, d₂) -
      (integerWeight (c₁, d₂) : R) * integerWeight (c₂, d₁) = 0 := by
    rw [h _ hm11, h _ hm22, h _ hm12, h _ hm21]
    ring
  obtain ⟨h11, h12, h21, h22⟩ := rectangle_values
  rw [h11, h12, h21, h22] at hz
  norm_num at hz

theorem normalized_certificate_not_product {R : Type*} [Field R] [CharZero R]
    (Z : R) (hZ : Z ≠ 0) :
    ¬ ∃ (K : R) (A B : Queue → R),
      ∀ s ∈ support, (integerWeight s : R) / Z = K * A s.1 * B s.2 := by
  rintro ⟨K, A, B, h⟩
  apply certificate_not_product (R := R)
  refine ⟨Z * K, A, B, ?_⟩
  intro s hs
  calc
    (integerWeight s : R) = (K * A s.1 * B s.2) * Z := (div_eq_iff hZ).mp (h s hs)
    _ = (Z * K) * A s.1 * B s.2 := by ring

end OddCycle.FiveJob
