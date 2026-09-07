import OddCycle.Model

/-! Orientations represented by their two-letter projections. This avoids
reasoning about numeric positions while jobs move through a queue. -/

namespace OddCycle

def edgeLetters (a b : Nat) (q : Queue) : Queue :=
  q.filter (fun x => x == a || x == b)

def EdgeEquiv (adj : Nat → Nat → Bool) (q r : Queue) : Prop :=
  ∀ a b, adj a b = true → edgeLetters a b q = edgeLetters a b r

theorem EdgeEquiv.refl (adj : Nat → Nat → Bool) (q : Queue) : EdgeEquiv adj q q :=
  fun _ _ _ => rfl

theorem EdgeEquiv.symm {adj : Nat → Nat → Bool} {q r : Queue}
    (h : EdgeEquiv adj q r) : EdgeEquiv adj r q := fun a b hab => (h a b hab).symm

theorem EdgeEquiv.trans {adj : Nat → Nat → Bool} {q r t : Queue}
    (h : EdgeEquiv adj q r) (h' : EdgeEquiv adj r t) : EdgeEquiv adj q t :=
  fun a b hab => (h a b hab).trans (h' a b hab)

theorem EdgeEquiv.append_left {adj : Nat → Nat → Bool} {q r : Queue}
    (h : EdgeEquiv adj q r) (p : Queue) : EdgeEquiv adj (p ++ q) (p ++ r) := by
  intro a b hab
  simp only [edgeLetters, List.filter_append]
  exact congrArg (_ ++ ·) (h a b hab)

theorem EdgeEquiv.append_right {adj : Nat → Nat → Bool} {q r : Queue}
    (h : EdgeEquiv adj q r) (p : Queue) : EdgeEquiv adj (q ++ p) (r ++ p) := by
  intro a b hab
  simp only [edgeLetters, List.filter_append]
  exact congrArg (· ++ _) (h a b hab)

theorem EdgeEquiv.cons {adj : Nat → Nat → Bool} {q r : Queue}
    (h : EdgeEquiv adj q r) (x : Nat) : EdgeEquiv adj (x :: q) (x :: r) :=
  h.append_left [x]

theorem EdgeEquiv.reverse {adj : Nat → Nat → Bool} {q r : Queue}
    (h : EdgeEquiv adj q r) : EdgeEquiv adj q.reverse r.reverse := by
  intro a b hab
  simpa [edgeLetters, List.filter_reverse] using congrArg List.reverse (h a b hab)

theorem edgeEquiv_swap {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) {x y : Nat} (hxy : adj x y = false)
    (q : Queue) : EdgeEquiv adj (x :: y :: q) (y :: x :: q) := by
  intro a b hab
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    by_cases hya : y = a <;> by_cases hyb : y = b <;>
    simp_all [edgeLetters]

theorem edgeEquiv_move {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) {job : Nat} {q : Queue}
    (h : ∀ x ∈ q, adj job x = false) : EdgeEquiv adj (job :: q) (q ++ [job]) := by
  induction q with
  | nil => exact EdgeEquiv.refl _ _
  | cons x xs ih =>
    exact (edgeEquiv_swap hsym (h x (by simp)) xs).trans
      ((ih (fun y hy => h y (by simp [hy]))).cons x)

/-- A topological order for the orientation induced by a vertex rank. -/
def RankOrdered (adj : Nat → Nat → Bool) (rank : Nat → Nat) (q : Queue) : Prop :=
  q.Pairwise (fun a b => adj a b = true → rank a < rank b)

/-- Edges that may cross after the replacement budget is exhausted. -/
def eraseEdge (adj : Nat → Nat → Bool) (p v a b : Nat) : Bool :=
  adj a b && !(a == p && b == v || a == v && b == p)

theorem eraseEdge_symm {adj : Nat → Nat → Bool}
    (hsym : ∀ a b, adj a b = adj b a) (p v a b : Nat) :
    eraseEdge adj p v a b = eraseEdge adj p v b a := by
  simp [eraseEdge, hsym a b, Bool.and_comm, Bool.or_comm]

/-- Each replacement increases the rank. Consequently only the designated
boundary edge can change after a budget of `threshold` replacements.
The theorem holds for arbitrary finite graphs and rank functions. -/
theorem carry_edgeEquiv_erase {adj : Nat → Nat → Bool} {rank : Nat → Nat}
    {allowed : Nat → Prop} {threshold p v : Nat}
    (hsym : ∀ a b, adj a b = adj b a)
    (hboundary : ∀ a b, allowed a → allowed b → threshold ≤ rank a → rank a < rank b →
      adj a b = true → (a = p ∧ b = v) ∨ (a = v ∧ b = p))
    (budget job : Nat) (q : Queue)
    (hallowed : ∀ x ∈ job :: q, allowed x)
    (hordered : RankOrdered adj rank (job :: q))
    (hbudget : threshold ≤ budget + rank job) :
    EdgeEquiv (eraseEdge adj p v) (job :: q)
      ((carry adj budget job q).1 ++ [(carry adj budget job q).2]) := by
  induction q generalizing budget job with
  | nil => exact EdgeEquiv.refl _ _
  | cons x xs ih =>
    have ho := List.pairwise_cons.mp hordered
    have hjx := ho.1 x (by simp)
    by_cases hz : budget = 0
    · simp only [carry, hz, if_true]
      apply edgeEquiv_move (eraseEdge_symm hsym p v)
      intro y hy
      by_cases ha : adj job y = true
      · have hb := hboundary job y (hallowed job (by simp))
          (hallowed y (by simp [hy])) (by omega) (ho.1 y hy ha) ha
        rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [eraseEdge]
      · simp [eraseEdge, ha]
    · by_cases ha : adj job x = true
      · have hi := ih (budget - 1) x
          (fun y hy => hallowed y (by simp [hy])) ho.2 (by have := hjx ha; omega)
        simpa [carry, hz, ha] using hi.cons job
      · have hi := ih budget job
          (fun y hy => hallowed y (by
            rcases List.mem_cons.mp hy with rfl | hy
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)))
          (List.pairwise_cons.mpr ⟨fun y hy => ho.1 y (by simp [hy]),
            (List.pairwise_cons.mp ho.2).2⟩) hbudget
        have hswap := edgeEquiv_swap (eraseEdge_symm hsym p v)
          (show eraseEdge adj p v job x = false by simp [eraseEdge, ha]) xs
        simpa [carry, hz, ha] using hswap.trans (hi.cons x)

theorem idxOf_filter_lt_iff (pred : Nat → Bool) (a b : Nat) (q : Queue)
    (ha : pred a = true) (hb : pred b = true) :
    (q.filter pred).idxOf a < (q.filter pred).idxOf b ↔ q.idxOf a < q.idxOf b := by
  induction q with
  | nil => simp
  | cons x xs ih =>
    by_cases hxa : x = a
    · subst x
      by_cases hab : a = b
      · subst b; simp
      · simp [ha, hab]
    · by_cases hxb : x = b
      · subst x
        simp [hb, hxa]
      · cases hp : pred x <;> simp [hp, hxa, hxb, ih]

theorem EdgeEquiv.before_iff {adj : Nat → Nat → Bool} {q r : Queue}
    (h : EdgeEquiv adj q r) {a b : Nat} (hab : adj a b = true) :
    q.idxOf a < q.idxOf b ↔ r.idxOf a < r.idxOf b := by
  have hq := idxOf_filter_lt_iff (fun x => x == a || x == b) a b q (by simp) (by simp)
  have hr := idxOf_filter_lt_iff (fun x => x == a || x == b) a b r (by simp) (by simp)
  change (edgeLetters a b r).idxOf a < (edgeLetters a b r).idxOf b ↔ _ at hr
  rw [← h a b hab] at hr
  exact hq.symm.trans hr

theorem EdgeEquiv.orientation_eq {n : Nat} {s t : State}
    (h : EdgeEquiv (cycleAdjacent n) (placement s) (placement t)) :
    orientation n s = orientation n t := by
  apply List.map_congr_left
  intro a _
  simp only [h.before_iff (a := a) (b := (a + 1) % n) (by simp [cycleAdjacent])]

theorem complete_edgeEquiv_erase {adj : Nat → Nat → Bool} {rank : Nat → Nat}
    {allowed : Nat → Prop} {threshold p v : Nat}
    (hsym : ∀ a b, adj a b = adj b a)
    (hboundary : ∀ a b, allowed a → allowed b → threshold ≤ rank a → rank a < rank b →
      adj a b = true → (a = p ∧ b = v) ∨ (a = v ∧ b = p))
    {q rest : Queue} {pos departed initiating : Nat}
    (hallowed : ∀ x ∈ q, allowed x) (hordered : RankOrdered adj rank q)
    (h : complete adj threshold q pos = some (rest, departed, initiating)) :
    EdgeEquiv (eraseEdge adj p v) q (rest ++ [departed]) := by
  induction q generalizing pos rest departed initiating with
  | nil => simp [complete] at h
  | cons x xs ih =>
    cases pos with
    | zero =>
      simp only [complete, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact carry_edgeEquiv_erase hsym hboundary threshold x xs hallowed hordered (by omega)
    | succ pos =>
      cases he : complete adj threshold xs pos with
      | none => simp [complete, he] at h
      | some result =>
        obtain ⟨r, d, i⟩ := result
        simp [complete, he] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        exact (ih (fun y hy => hallowed y (by simp [hy]))
          (List.pairwise_cons.mp hordered).2 he).cons x

theorem transition_first_edgeEquiv_erase {adj : Nat → Nat → Bool} {rank : Nat → Nat}
    {allowed : Nat → Prop} {threshold p v : Nat}
    (hsym : ∀ a b, adj a b = adj b a)
    (hboundary : ∀ a b, allowed a → allowed b → threshold ≤ rank a → rank a < rank b →
      adj a b = true → (a = p ∧ b = v) ∨ (a = v ∧ b = p))
    {s t : State} {pos initiating : Nat}
    (hallowed : ∀ x ∈ s.1, allowed x)
    (hordered : RankOrdered adj rank (placement s))
    (h : transition adj threshold s false pos = some (t, initiating)) :
    EdgeEquiv (eraseEdge adj p v) (placement s) (placement t) := by
  cases he : complete adj threshold s.1 pos with
  | none => simp [transition, he] at h
  | some result =>
    obtain ⟨r, d, i⟩ := result
    simp [transition, he] at h
    rcases h with ⟨rfl, rfl⟩
    have ho := (List.pairwise_append.mp hordered).1
    have hc := complete_edgeEquiv_erase hsym hboundary hallowed ho he
    simpa [placement, List.append_assoc] using hc.append_right s.2.reverse

end OddCycle
