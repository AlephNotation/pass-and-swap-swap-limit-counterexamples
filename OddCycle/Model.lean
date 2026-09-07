import Mathlib.Data.List.Permutation
import Mathlib.Algebra.Field.Rat
import Mathlib.Logic.Relation

/-!
The operational model. Queues run from head to tail. A completion removes its
initiating job, carries it strictly toward the tail, and replaces the first
compatible job until the replacement budget is exhausted. The initiating
completion does not consume that budget.

The definitions are total: an out-of-range position has no completion.
No transition table or Python result is used to define the dynamics.
-/

namespace OddCycle

abbrev Queue := List Nat
abbrev State := Queue × Queue

def cycleAdjacent (n a b : Nat) : Bool :=
  (a + 1) % n == b || (b + 1) % n == a

/-- Scan the untouched suffix; a replacement consumes exactly one unit. -/
def carry (adj : Nat → Nat → Bool) (budget job : Nat) : Queue → Queue × Nat
  | [] => ([], job)
  | x :: xs =>
    if budget = 0 then (x :: xs, job)
    else if adj job x then
      let (rest, departed) := carry adj (budget - 1) x xs
      (job :: rest, departed)
    else
      let (rest, departed) := carry adj budget job xs
      (x :: rest, departed)

/-- Remaining queue, departing job, and initiating job. -/
def complete (adj : Nat → Nat → Bool) (budget : Nat) :
    Queue → Nat → Option (Queue × Nat × Nat)
  | [], _ => none
  | x :: xs, 0 =>
    let (rest, departed) := carry adj budget x xs
    some (rest, departed, x)
  | x :: xs, p + 1 => do
    let (rest, departed, initiating) ← complete adj budget xs p
    pure (x :: rest, departed, initiating)

/-- An event retains the initiating class, which determines its service rate. -/
abbrev Event := State × Nat

def transition (adj : Nat → Nat → Bool) (budget : Nat) (s : State)
    (second : Bool) (pos : Nat) : Option Event := do
  let (rest, departed, initiating) ← complete adj budget (if second then s.2 else s.1) pos
  pure (if second then ((s.1 ++ [departed], rest), initiating)
        else ((rest, s.2 ++ [departed]), initiating))

def events (adj : Nat → Nat → Bool) (budget : Nat) (s : State) : List Event :=
  ((List.range s.1.length).filterMap (transition adj budget s false)) ++
  ((List.range s.2.length).filterMap (transition adj budget s true))

/-- The fixed-population state space: each label occurs exactly once. -/
def Valid (n : Nat) (s : State) : Prop := (s.1 ++ s.2).Perm (List.range n)

instance (n : Nat) (s : State) : Decidable (Valid n s) :=
  inferInstanceAs (Decidable ((s.1 ++ s.2).Perm (List.range n)))

def allStates (n : Nat) : List State :=
  (List.range n).permutations'.flatMap fun q =>
    (List.range (n + 1)).map fun k => (q.take k, q.drop k)

theorem mem_allStates_iff {n : Nat} {s : State} : s ∈ allStates n ↔ Valid n s := by
  constructor
  · intro h
    obtain ⟨q, hq, hk⟩ := List.mem_flatMap.mp h
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hk
    simpa [Valid] using List.mem_permutations'.mp hq
  · intro h
    apply List.mem_flatMap.mpr
    refine ⟨s.1 ++ s.2, List.mem_permutations'.mpr h, ?_⟩
    apply List.mem_map.mpr
    refine ⟨s.1.length, ?_, ?_⟩
    · have hl := h.length_eq
      simp only [List.length_append, List.length_range] at hl
      simp only [List.mem_range]
      omega
    · simp

def placement (s : State) : Queue := s.1 ++ s.2.reverse

/-- Direction of each cycle edge, in the order (0,1), ..., (n-1,0). -/
def orientation (n : Nat) (s : State) : List Bool :=
  (List.range n).map fun a =>
    decide ((placement s).idxOf a < (placement s).idxOf ((a + 1) % n))

/-- The longer branch's internal vertices precede the shorter branch's.
`forward = false` reflects the entire orientation. -/
def branchWord (w source : Nat) (forward : Bool) : Queue :=
  let n := 2 * w + 1
  let label := fun k => (source + if forward then k else n - k) % n
  [source] ++ (List.range w).map (fun j => label (j + 1)) ++
    (List.range (w - 1)).map (fun j => label (n - (j + 1))) ++ [label (w + 1)]

/-- The orientation is two source-to-sink branches of lengths w and w+1. -/
def balanced (w : Nat) (s : State) : Bool :=
  (List.range (2 * w + 1)).any fun source =>
    [true, false].any fun forward =>
      orientation (2 * w + 1) s ==
        orientation (2 * w + 1) (branchWord w source forward, [])

def pathEdges (adj : Nat → Nat → Bool) : Queue → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => adj x y && pathEdges adj (y :: xs)

/-- Every directed path is an adjacency chain in a subsequence of placement. -/
def height (n : Nat) (s : State) : Nat :=
  (((placement s).sublists.filter (pathEdges (cycleAdjacent n))).map
    (fun p => p.length - 1)).foldl max 0

variable {K : Type*} [Field K]

/-- Canonical prefix-product weight; `total` is the preceding prefix rate. -/
def prefixWeight (rate : Nat → K) (total : K) : Queue → K
  | [] => 1
  | x :: xs => (total + rate x)⁻¹ * prefixWeight rate (total + rate x) xs

def canonicalWeight (rate : Nat → K) (s : State) : K :=
  prefixWeight rate 0 s.1 * prefixWeight rate 0 s.2

/-- Row-generator balance at a target; repeated destinations are separate events.
Subtracting the outgoing event flow also correctly handles any self-events. -/
def balance (adj : Nat → Nat → Bool) (budget : Nat) (rate : Nat → K)
    (states : List State) (weight : State → K) (target : State) : K :=
  (states.map fun s =>
    ((events adj budget s).map fun e =>
      (if e.1 = target then weight s * rate e.2 else 0) -
      (if s = target then weight s * rate e.2 else 0)).sum).sum

def Stationary (adj : Nat → Nat → Bool) (budget : Nat) (rate : Nat → K)
    (states : List State) (weight : State → K) : Prop :=
  ∀ target ∈ states, balance adj budget rate states weight target = 0

end OddCycle
