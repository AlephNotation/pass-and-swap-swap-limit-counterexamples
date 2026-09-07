import OddCycle.ModulatedCertificate
import OddCycle.FiveJob
import OddCycle.UnlimitedCarry
import OddCycle.FiniteStationary
import OddCycle.Reachability
import Mathlib.Data.Fintype.List

/-! A nondegenerate two-state Markov modulation counterexample on C₅.
False means budget two; true means unlimited (five covers every queue).
The environment flips at rate one independently of the queue state. Each
queue completion has the initiating job's rate: two for 0, one otherwise.
All certificate equations are checked against these operational events. -/

namespace OddCycle.ModulatedFiveJob

set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- Keep finite kernel checks sequential so their reduction caches can be released.
set_option Elab.async false

def support : List JointState :=
  FiveJob.support.map (fun s => (s, false)) ++ FiveJob.support.map (fun s => (s, true))

theorem witness_states : witnesses.map Witness.state = support := by decide +kernel

def integerWeight (s : JointState) : Nat :=
  ((witnesses.find? (fun row => row.state == s)).map Witness.weight).getD 0

def jobRate (job : Nat) : Nat := if job = 0 then 2 else 1

def modeEvents (s : JointState) : List (JointState × Nat) :=
  ((events FiveJob.adj (if s.2 then 5 else 2) s.1).map
    fun e => ((e.1, s.2), jobRate e.2)) ++ [((s.1, !s.2), 1)]

def incomingRate (s t : JointState) : Nat :=
  ((modeEvents s).map fun e => if e.1 = t then e.2 else 0).sum

private theorem of_witnesses {p : JointState → Prop}
    (h : ∀ row ∈ witnesses, p row.state) : ∀ s ∈ support, p s := by
  intro s hs
  rw [← witness_states] at hs
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hs
  exact h row hrow

theorem support_size : support.length = 360 := by
  simp [support, FiveJob.support_size]

theorem support_nodup : support.Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨FiveJob.support_nodup.map (fun _ _ h => congrArg Prod.fst h),
    FiveJob.support_nodup.map (fun _ _ h => congrArg Prod.fst h), ?_⟩
  intro s hfalse htrue
  obtain ⟨u, _, hu⟩ := List.mem_map.mp hfalse
  obtain ⟨v, _, hv⟩ := List.mem_map.mp htrue
  have h := congrArg Prod.snd (hu.trans hv.symm)
  contradiction

theorem mem_support_iff {s : JointState} : s ∈ support ↔ s.1 ∈ FiveJob.support := by
  rcases s with ⟨q, b⟩
  cases b <;> simp [support]

theorem support_projection : ∀ s ∈ support, s.1 ∈ FiveJob.support :=
  fun _ h => mem_support_iff.mp h

theorem support_modes : ∀ s ∈ FiveJob.support, ∀ b : Bool, (s, b) ∈ support :=
  fun _ h _ => mem_support_iff.mpr h

theorem support_closed :
    ∀ s ∈ support, ∀ e ∈ modeEvents s, e.1 ∈ support := by
  apply of_witnesses
  simp only [witnesses, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals as_aux_lemma => decide +kernel

theorem total_event_rate :
    ∀ s ∈ support, ((modeEvents s).map Prod.snd).sum = 7 := by
  apply of_witnesses
  simp only [witnesses, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals as_aux_lemma => decide +kernel

def unlimitedComplete : Queue → Nat → Option (Queue × Nat × Nat)
  | [], _ => none
  | job :: rest, 0 =>
    let e := unlimitedCarry FiveJob.adj job rest
    some (e.1, e.2, job)
  | job :: rest, pos + 1 => do
    let (q, departed, initiating) ← unlimitedComplete rest pos
    pure (job :: q, departed, initiating)

/-- Budget five is the actual unlimited scan on every queue of this model. -/
theorem complete_unlimited (q : Queue) (pos : Nat) (hq : q.length ≤ 5) :
    complete FiveJob.adj 5 q pos = unlimitedComplete q pos := by
  induction q generalizing pos with
  | nil => rfl
  | cons job rest ih =>
    cases pos with
    | zero =>
      simp only [complete, unlimitedComplete,
        carry_eq_unlimited FiveJob.adj rest job 5 (by simp at hq; omega)]
    | succ pos =>
      simp only [complete, unlimitedComplete, ih pos (by simp at hq; omega)]

theorem supported_queue_lengths :
    ∀ s ∈ support, s.1.1.length ≤ 5 ∧ s.1.2.length ≤ 5 := by
  apply of_witnesses
  simp only [witnesses, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals as_aux_lemma => decide +kernel

def Step (s t : JointState) : Prop := ∃ rate, (t, rate) ∈ modeEvents s ∧ 0 < rate
abbrev Reachable := Relation.ReflTransGen Step

theorem step_closed {s t : JointState} (hs : s ∈ support) (h : Step s t) : t ∈ support := by
  obtain ⟨rate, he, _⟩ := h
  exact support_closed s hs (t, rate) he

theorem reachable_closed {s t : JointState} (hs : s ∈ support) (h : Reachable s t) : t ∈ support := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact step_closed ih hstep

theorem switch_step (s : JointState) : Step s (s.1, !s.2) := by
  exact ⟨1, List.mem_append_right _ (by simp), by decide⟩

theorem limited_head_step {s t : State} (h : FiveJob.HeadStep s t) : Step (s, false) (t, false) := by
  obtain ⟨side, job, he⟩ := h
  obtain ⟨initiating, hm⟩ := EventStep.iff_mem.mp ⟨side, 0, job, he⟩
  refine ⟨jobRate initiating, ?_, ?_⟩
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨(t, initiating), hm, rfl⟩
  · unfold jobRate
    split <;> decide

theorem communication {s t : JointState} (hs : s ∈ support) (ht : t ∈ support) : Reachable s t := by
  have hstart : Reachable s (s.1, false) := by
    rcases s with ⟨q, b⟩
    cases b
    · exact .refl
    · exact .single (switch_step (q, true))
  have hend : Reachable (t.1, false) t := by
    rcases t with ⟨q, b⟩
    cases b
    · exact .refl
    · exact .single (switch_step (q, false))
  have middle := FiveJob.head_communication (support_projection s hs) (support_projection t ht)
  exact hstart.trans ((middle.lift (fun q => (q, false)) (fun _ _ h => limited_head_step h)).trans hend)

theorem certificate_positive : ∀ s ∈ support, 0 < integerWeight s := by
  apply of_witnesses
  simp only [witnesses, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals as_aux_lemma => decide +kernel
theorem certificate_total : (support.map integerWeight).sum = totalWeight := by decide +kernel

theorem witness_weight : ∀ row ∈ witnesses, integerWeight row.state = row.weight := by
  simp only [witnesses, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals as_aux_lemma => decide +kernel

def incomingWeight (t : JointState) : Nat :=
  (witnesses.map fun row => row.weight * incomingRate row.state t).sum

theorem incomingWeight_eq (t : JointState) : incomingWeight t =
    (support.map fun s => integerWeight s * incomingRate s t).sum := by
  unfold incomingWeight
  rw [← witness_states, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro row hrow
  change row.weight * incomingRate row.state t =
    integerWeight row.state * incomingRate row.state t
  rw [witness_weight row hrow]

/-- Every full-state integer balance equation, without trusting the orbit solver. -/
theorem certificate_balance : ∀ t ∈ support,
    (support.map fun s => integerWeight s * incomingRate s t).sum = 7 * integerWeight t := by
  have checked : ∀ row ∈ witnesses,
      incomingWeight row.state = 7 * integerWeight row.state := by
    simp only [witnesses, List.forall_mem_cons]
    repeat' apply And.intro
    all_goals as_aux_lemma => decide +kernel
  intro t ht
  rw [← witness_states] at ht
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp ht
  exact (incomingWeight_eq row.state).symm.trans (checked row hrow)

theorem limited_mode_total :
    ((support.filter fun s => !s.2).map integerWeight).sum = totalWeight / 2 := by decide +kernel

def r₁₁ : JointState := ((FiveJob.c₁, FiveJob.d₁), false)
def r₁₂ : JointState := ((FiveJob.c₁, FiveJob.d₂), false)
def r₂₁ : JointState := ((FiveJob.c₂, FiveJob.d₁), false)
def r₂₂ : JointState := ((FiveJob.c₂, FiveJob.d₂), false)

theorem rectangle_mem : r₁₁ ∈ support ∧ r₁₂ ∈ support ∧ r₂₁ ∈ support ∧ r₂₂ ∈ support := by decide +kernel

theorem rectangle_values :
    integerWeight r₁₁ = 1348685591611876148089748859734044719271023310 ∧
    integerWeight r₁₂ = 1348431658413767858611132306611249507792610780 ∧
    integerWeight r₂₁ = 3857602895353586455373269034123100338407161060 ∧
    integerWeight r₂₂ = 3859614253453951091430083613590818106401845720 := by decide +kernel

/-- Even the queue factors and prefactor may depend on the environment mode. -/
theorem certificate_not_product {R : Type*} [Field R] [CharZero R] :
    ¬ ∃ (K : Bool → R) (A B : Bool → Queue → R), ∀ s ∈ support,
      (integerWeight s : R) = K s.2 * A s.2 s.1.1 * B s.2 s.1.2 := by
  rintro ⟨K, A, B, h⟩
  obtain ⟨ha, hb, hc, hd⟩ := rectangle_mem
  have hz : (integerWeight r₁₁ : R) * integerWeight r₂₂ -
      (integerWeight r₁₂ : R) * integerWeight r₂₁ = 0 := by
    rw [h _ ha, h _ hd, h _ hb, h _ hc]
    simp only [r₁₁, r₁₂, r₂₁, r₂₂]
    ring
  obtain ⟨ha, hb, hc, hd⟩ := rectangle_values
  rw [ha, hd, hb, hc] at hz
  norm_num at hz

theorem normalized_certificate_not_product {R : Type*} [Field R] [CharZero R]
    (Z : R) (hZ : Z ≠ 0) :
    ¬ ∃ (K : Bool → R) (A B : Bool → Queue → R), ∀ s ∈ support,
      (integerWeight s : R) / Z = K s.2 * A s.2 s.1.1 * B s.2 s.1.2 := by
  rintro ⟨K, A, B, h⟩
  apply certificate_not_product (R := R)
  refine ⟨fun b => Z * K b, A, B, ?_⟩
  intro s hs
  have he := (div_eq_iff hZ).mp (h s hs)
  rw [he]
  ring

end OddCycle.ModulatedFiveJob
