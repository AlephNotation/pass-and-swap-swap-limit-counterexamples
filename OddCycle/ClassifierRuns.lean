import OddCycle.ClassifierRank

/-! Costed list passes for placement construction and circular run extraction.
No call to an uncosted traversal is hidden inside these implementations. -/

namespace OddCycle.CycleClassifier

variable {α : Type}

def appendWork : List α → List α → Work (List α)
  | [], b => ⟨b, 1⟩
  | x :: a, b => let r := appendWork a b; ⟨x :: r.value, r.cost + 2⟩

theorem appendWork_spec (a b : List α) :
    (appendWork a b).value = a ++ b ∧ (appendWork a b).cost = 2 * a.length + 1 := by
  induction a with
  | nil => simp [appendWork]
  | cons x a ih => simp [appendWork, ih]; omega

def reverseWork : List α → List α → Work (List α)
  | [], a => ⟨a, 1⟩
  | x :: q, a => let r := reverseWork q (x :: a); ⟨r.value, r.cost + 2⟩

theorem reverseWork_spec (q a : List α) :
    (reverseWork q a).value = q.reverse ++ a ∧ (reverseWork q a).cost = 2 * q.length + 1 := by
  induction q generalizing a with
  | nil => simp [reverseWork]
  | cons x q ih => simp [reverseWork, ih, List.reverse_cons, List.append_assoc]; omega

def placementWork (s : State) : Work (List Nat) :=
  let r := reverseWork s.2 []
  let a := appendWork s.1 r.value
  ⟨a.value, r.cost + a.cost + 1⟩

theorem placementWork_spec (s : State) :
    (placementWork s).value = placement s ∧
    (placementWork s).cost = 2 * (s.1.length + s.2.length) + 3 := by
  dsimp only [placementWork]
  rw [(appendWork_spec _ _).1, (appendWork_spec _ _).2,
    (reverseWork_spec _ _).1, (reverseWork_spec _ _).2]
  simp only [List.append_nil, placement, true_and]
  omega

def splitWork : Nat → List α → Work (List α × List α)
  | 0, q => ⟨([], q), 1⟩
  | _ + 1, [] => ⟨([], []), 1⟩
  | i + 1, x :: q => let r := splitWork i q; ⟨(x :: r.value.1, r.value.2), r.cost + 3⟩

theorem splitWork_spec (i : Nat) (q : List α) :
    (splitWork i q).value = (q.take i, q.drop i) ∧ (splitWork i q).cost ≤ 3 * q.length + 1 := by
  induction i generalizing q with
  | zero => simp [splitWork]
  | succ i ih =>
    cases q with
    | nil => simp [splitWork]
    | cons x q =>
      have hh := ih q
      simp only [splitWork, hh.1, List.take_succ_cons, List.drop_succ_cons, List.length_cons,
        true_and]
      omega

def rotateWork (q : List α) (i : Nat) : Work (List α) :=
  let s := splitWork i q
  let a := appendWork s.value.2 s.value.1
  ⟨a.value, s.cost + a.cost + 1⟩

theorem rotateWork_spec (q : List α) (i : Nat) (hi : i ≤ q.length) :
    (rotateWork q i).value = q.rotate i ∧ (rotateWork q i).cost ≤ 5 * q.length + 3 := by
  have hs := splitWork_spec i q
  have ha := appendWork_spec (splitWork i q).value.2 (splitWork i q).value.1
  constructor
  · dsimp only [rotateWork]
    rw [ha.1, hs.1]
    exact (List.rotate_eq_drop_append_take hi).symm
  · dsimp only [rotateWork]
    rw [ha.2, hs.1]
    simp only [List.length_drop]
    omega

def lengthsWork (b : Bool) : List Bool → Work (List Nat)
  | [] => ⟨[1], 1⟩
  | c :: q =>
    let r := lengthsWork c q
    ⟨if b = c then CircularWord.bump r.value else 1 :: r.value, r.cost + 4⟩

theorem lengthsWork_spec (b : Bool) (q : List Bool) :
    (lengthsWork b q).value = CircularWord.lengthsFrom b q ∧
    (lengthsWork b q).cost = 4 * q.length + 1 := by
  induction q generalizing b with
  | nil => simp [lengthsWork, CircularWord.lengthsFrom]
  | cons c q ih => simp [lengthsWork, CircularWord.lengthsFrom, ih]; omega

def linearWork : List Bool → Work (List Nat)
  | [] => ⟨[], 1⟩
  | b :: q => let r := lengthsWork b q; ⟨r.value, r.cost + 1⟩

theorem linearWork_spec (q : List Bool) :
    (linearWork q).value = CircularWord.linearRuns q ∧ (linearWork q).cost ≤ 4 * q.length + 1 := by
  cases q with
  | nil => simp [linearWork, CircularWord.linearRuns]
  | cons b q => simp [linearWork, CircularWord.linearRuns, lengthsWork_spec]

def runsWork (q : List Bool) : Work (List Nat) :=
  let l := linearWork q
  let r := rotateWork q (l.value.headD 0)
  let t := linearWork r.value
  ⟨t.value, l.cost + r.cost + t.cost + 2⟩

theorem runsWork_spec (q : List Bool) :
    (runsWork q).value = CircularWord.circularRuns q ∧ (runsWork q).cost ≤ 13 * q.length + 7 := by
  have hl := linearWork_spec q
  have hhead : (CircularWord.linearRuns q).headD 0 ≤ q.length := by
    rw [← CircularWord.linearRuns_sum q]
    cases CircularWord.linearRuns q <;> simp
  have hr := rotateWork_spec q ((linearWork q).value.headD 0) (by simpa only [hl.1] using hhead)
  have ht := linearWork_spec (rotateWork q ((linearWork q).value.headD 0)).value
  constructor
  · dsimp only [runsWork]
    rw [ht.1, hr.1, hl.1]
    rfl
  · have hlen : (rotateWork q ((linearWork q).value.headD 0)).value.length = q.length := by
      rw [hr.1, List.length_rotate]
    simp only [runsWork]
    omega

end OddCycle.CycleClassifier
