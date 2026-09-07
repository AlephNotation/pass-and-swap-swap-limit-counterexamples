import OddCycle.CycleRunStates
import Init.Data.Array.Lemmas

/-! A rank table built by one pass over the placement. Costs count bounded
word-RAM operations: list inspection/cons, array reads/writes, word arithmetic
and comparisons. Array allocation is charged by its size. The table has one
owner during construction, as required for constant-time mutable RAM writes.
These are algorithmic costs, not bounds on Lean kernel reduction or arbitrary-
precision bit complexity. -/

namespace OddCycle.CycleClassifier

structure Work (α : Type) where
  value : α
  cost : Nat
  deriving Repr

def rankLoop : List Nat → Nat → Array Nat → Work (Array Nat)
  | [], _, a => ⟨a, 1⟩
  | x :: q, j, a =>
    let r := rankLoop q (j + 1) (a.setIfInBounds x j)
    ⟨r.value, r.cost + 3⟩

theorem rankLoop_cost (q : List Nat) (j : Nat) (a : Array Nat) :
    (rankLoop q j a).cost = 3 * q.length + 1 := by
  induction q generalizing j a with
  | nil => rfl
  | cons x q ih => simp [rankLoop, ih]; omega

theorem rankLoop_size (q : List Nat) (j : Nat) (a : Array Nat) :
    (rankLoop q j a).value.size = a.size := by
  induction q generalizing j a with
  | nil => rfl
  | cons x q ih => simp [rankLoop, ih]

theorem rankLoop_get (q : List Nat) (hq : q.Nodup) (j : Nat) (a : Array Nat)
    (x : Nat) (hx : x < a.size) :
    (rankLoop q j a).value[x]'(by rw [rankLoop_size]; exact hx) =
      if x ∈ q then j + q.idxOf x else a[x] := by
  induction q generalizing j a with
  | nil => simp [rankLoop]
  | cons y q ih =>
    have hnd := List.nodup_cons.mp hq
    change (rankLoop q (j + 1) (a.setIfInBounds y j)).value[x]'(by rw [rankLoop_size]; simpa using hx) = _
    rw [ih hnd.2 _ _ (by simpa using hx)]
    by_cases he : y = x
    · subst y
      simp [hnd.1]
    · simp only [List.mem_cons, eq_comm (a := x) (b := y), he, false_or,
        List.idxOf_cons_ne q he, Array.getElem_setIfInBounds_ne hx he]
      split_ifs <;> omega

def ranks (n : Nat) (q : List Nat) : Work (Array Nat) :=
  let r := rankLoop q 0 (Array.replicate n 0)
  ⟨r.value, r.cost + n⟩

theorem ranks_size (n : Nat) (q : List Nat) : (ranks n q).value.size = n := by
  simp [ranks, rankLoop_size]

theorem ranks_get {n : Nat} {q : List Nat} (hq : q.Perm (List.range n)) (x : Nat) (hx : x < n) :
    (ranks n q).value[x]'(by rw [ranks_size]; exact hx) = q.idxOf x := by
  have hm : x ∈ q := hq.mem_iff.mpr (List.mem_range.mpr hx)
  have hnd := hq.nodup_iff.mpr List.nodup_range
  exact (rankLoop_get q hnd 0 (Array.replicate n 0) x (by simpa using hx)).trans (by simp [hm])

theorem ranks_cost (n : Nat) (q : List Nat) : (ranks n q).cost = n + 3 * q.length + 1 := by
  simp [ranks, rankLoop_cost]; omega

def bitsLoop (n : Nat) (a : Array Nat) : Nat → Nat → Work (List Bool)
  | 0, _ => ⟨[], 1⟩
  | m + 1, i =>
    let r := bitsLoop n a m (i + 1)
    ⟨decide (a[i]! < a[(i + 1) % n]!) :: r.value, r.cost + 6⟩

theorem bitsLoop_value (n : Nat) (a : Array Nat) (m i : Nat) :
    (bitsLoop n a m i).value = (List.range' i m).map (fun j => decide (a[j]! < a[(j + 1) % n]!)) := by
  induction m generalizing i with
  | zero => simp [bitsLoop]
  | succ m ih => simp [bitsLoop, List.range'_succ, ih]

theorem bitsLoop_cost (n : Nat) (a : Array Nat) (m i : Nat) :
    (bitsLoop n a m i).cost = 6 * m + 1 := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih => simp [bitsLoop, ih]; omega

theorem ranked_orientation {n : Nat} {s : State} (hn : 0 < n) (hs : Valid n s) :
    (bitsLoop n (ranks n (placement s)).value n 0).value = orientation n s := by
  rw [bitsLoop_value, ← List.range_eq_range']
  apply List.map_congr_left
  intro i hi
  have h₁ := List.mem_range.mp hi
  have h₂ := Nat.mod_lt (i + 1) hn
  have h₁' : i < (ranks n (placement s)).value.size := by rw [ranks_size]; exact h₁
  have h₂' : (i + 1) % n < (ranks n (placement s)).value.size := by rw [ranks_size]; exact h₂
  rw [getElem!_pos (ranks n (placement s)).value i h₁', getElem!_pos (ranks n (placement s)).value ((i + 1) % n) h₂',
    ranks_get hs.placement_perm i h₁, ranks_get hs.placement_perm _ h₂]

end OddCycle.CycleClassifier
