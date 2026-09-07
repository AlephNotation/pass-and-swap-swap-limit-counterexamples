import OddCycle.Balance

/-! Initiating labels and outgoing weighted rates do not depend on the
replacement budget. List sums retain every queue-position event. -/

namespace OddCycle

theorem complete_initiating (adj : Nat → Nat → Bool) (budget : Nat) (q : Queue) (pos : Nat) :
    (complete adj budget q pos).map (fun r => r.2.2) = q[pos]? := by
  induction q generalizing pos with
  | nil => simp [complete]
  | cons x xs ih =>
    cases pos with
    | zero => simp [complete]
    | succ pos =>
      cases he : complete adj budget xs pos with
      | none => simpa [complete, he] using ih pos
      | some result =>
        obtain ⟨r, d, i⟩ := result
        simpa [complete, he] using ih pos

theorem transition_initiating (adj : Nat → Nat → Bool) (budget : Nat) (s : State) (side : Bool) (pos : Nat) :
    (transition adj budget s side pos).map Prod.snd = (if side then s.2 else s.1)[pos]? := by
  rw [← complete_initiating adj budget (if side then s.2 else s.1) pos]
  cases he : complete adj budget (if side then s.2 else s.1) pos with
  | none => simp [transition, he]
  | some result =>
    obtain ⟨r, d, i⟩ := result
    simp [transition, he]
    split <;> rfl

theorem events_initiating_budget (adj : Nat → Nat → Bool) (first second : Nat) (s : State) :
    (events adj first s).map Prod.snd = (events adj second s).map Prod.snd := by
  simp only [events, List.map_append, List.map_filterMap]
  congr 1 <;> congr 1 <;> funext pos <;> exact (transition_initiating adj first s _ pos).trans
    (transition_initiating adj second s _ pos).symm

theorem filterMap_getElem_range (q : Queue) : (List.range q.length).filterMap (fun p => q[p]?) = q := by
  induction q with
  | nil => rfl
  | cons x xs ih =>
    simpa [List.range_succ_eq_map, List.filterMap_map, Function.comp_def] using congrArg (x :: ·) ih

theorem events_initiating (adj : Nat → Nat → Bool) (budget : Nat) (s : State) :
    (events adj budget s).map Prod.snd = s.1 ++ s.2 := by
  simp only [events, List.map_append, List.map_filterMap, transition_initiating,
    Bool.false_eq_true, ↓reduceIte, filterMap_getElem_range]

variable {K : Type*} [Field K]

def incomingOption (rate : Nat → K) (weight : K) (target : State) (event : Option Event) : K :=
  (event.map (fun e => if e.1 = target then weight * rate e.2 else 0)).getD 0

def incomingRow (adj : Nat → Nat → Bool) (budget : Nat) (rate : Nat → K)
    (weight : K) (target source : State) : K :=
  ((events adj budget source).map (fun e => if e.1 = target then weight * rate e.2 else 0)).sum

theorem sum_filterMap {α β : Type*} (l : List α) (f : α → Option β) (g : β → K) :
    ((l.filterMap f).map g).sum = (l.map (fun x => ((f x).map g).getD 0)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases he : f x <;> simp [he, ih]

theorem incomingRow_positions (adj : Nat → Nat → Bool) (budget : Nat) (rate : Nat → K)
    (weight : K) (target source : State) :
    incomingRow adj budget rate weight target source =
      ((List.range source.1.length).map (fun pos => incomingOption rate weight target
        (transition adj budget source false pos))).sum +
      ((List.range source.2.length).map (fun pos => incomingOption rate weight target
        (transition adj budget source true pos))).sum := by
  simp only [incomingRow, events, List.map_append, List.sum_append, sum_filterMap, incomingOption]

theorem sum_map_sub {α : Type*} (q : List α) (f g : α → K) :
    (q.map (fun x => f x - g x)).sum = (q.map f).sum - (q.map g).sum := by
  induction q with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem balance_difference_incoming (adj : Nat → Nat → Bool) (first second : Nat) (rate : Nat → K)
    (states : List State) (weight : State → K) (target : State) :
    balance adj first rate states weight target - balance adj second rate states weight target =
      (states.map (fun s => incomingRow adj first rate (weight s) target s -
        incomingRow adj second rate (weight s) target s)).sum := by
  unfold balance
  rw [← sum_map_sub]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  have hout : ((events adj first s).map (fun e => if s = target then weight s * rate e.2 else 0)).sum =
      ((events adj second s).map (fun e => if s = target then weight s * rate e.2 else 0)).sum := by
    have h := congrArg (fun labels : List Nat => (labels.map (fun i => if s = target then weight s * rate i else 0)).sum)
      (events_initiating_budget adj first second s)
    simpa only [List.map_map, Function.comp_def] using h
  rw [sum_map_sub, sum_map_sub, hout]
  simp only [incomingRow]
  ring

theorem incomingOption_zero {rate : Nat → K} {weight : K} {target : State} {event : Option Event}
    (h : ∀ i, event ≠ some (target, i)) : incomingOption rate weight target event = 0 := by
  cases event with
  | none => rfl
  | some e =>
    obtain ⟨t, i⟩ := e
    have ht : t ≠ target := by intro he; subst t; exact h i rfl
    simp [incomingOption, ht]

theorem sum_map_single {α : Type*} [DecidableEq α] {q : List α} (hn : q.Nodup)
    (x : α) (value : K) :
    (q.map (fun y => if y = x then value else 0)).sum = if x ∈ q then value else 0 := by
  induction q with
  | nil => simp
  | cons y ys ih =>
    have hp := List.nodup_cons.mp hn
    by_cases he : y = x
    · subst y
      simp [ih hp.2, hp.1]
    · simp [he, Ne.symm he, ih hp.2]

end OddCycle
