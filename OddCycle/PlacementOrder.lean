import OddCycle.Operational
import OddCycle.EdgeOrder
import Mathlib.Data.List.Nodup

namespace OddCycle

theorem Valid.placement_perm {n : Nat} {s : State} (h : Valid n s) :
    (placement s).Perm (List.range n) :=
  ((List.reverse_perm s.2).append_left s.1).trans h

theorem Valid.placement_mem {n x : Nat} {s : State} (h : Valid n s) :
    x ∈ placement s ↔ x < n := h.placement_perm.mem_iff.trans List.mem_range

theorem Valid.placement_nodup {n : Nat} {s : State} (h : Valid n s) :
    (placement s).Nodup := h.placement_perm.nodup_iff.mpr List.nodup_range

theorem RankOrdered.before {adj : Nat → Nat → Bool} {rank : Nat → Nat} {q : Queue}
    (h : RankOrdered adj rank q) {a b : Nat} (ha : a ∈ q) (hb : b ∈ q)
    (hbefore : q.idxOf a < q.idxOf b) (hab : adj a b = true) : rank a < rank b := by
  have hr := List.pairwise_iff_getElem.mp h (q.idxOf a) (q.idxOf b)
    (List.idxOf_lt_length_of_mem ha) (List.idxOf_lt_length_of_mem hb) hbefore
  have hr' : adj a b = true → rank a < rank b := by simpa using hr
  exact hr' hab

theorem rankOrdered_of_before {adj : Nat → Nat → Bool} {rank : Nat → Nat} {q : Queue}
    (hnd : q.Nodup)
    (h : ∀ a ∈ q, ∀ b ∈ q, q.idxOf a < q.idxOf b → adj a b = true → rank a < rank b) :
    RankOrdered adj rank q := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij hab
  exact h q[i] (List.getElem_mem hi) q[j] (List.getElem_mem hj)
    (by simpa only [hnd.idxOf_getElem i hi, hnd.idxOf_getElem j hj] using hij) hab

theorem orientation_edge_iff {n : Nat} {s t : State}
    (h : orientation n s = orientation n t) {a : Nat} (ha : a < n) :
    (placement s).idxOf a < (placement s).idxOf ((a + 1) % n) ↔
      (placement t).idxOf a < (placement t).idxOf ((a + 1) % n) := by
  have he := congrArg (fun q : List Bool => q[a]?) h
  have hd : decide ((placement s).idxOf a < (placement s).idxOf ((a + 1) % n)) =
      decide ((placement t).idxOf a < (placement t).idxOf ((a + 1) % n)) := by
    simpa [orientation, ha] using he
  simpa using (congrArg (fun b : Bool => b = true) hd).to_iff

theorem orientation_before_iff {n : Nat} {s t : State} (hs : Valid n s) (ht : Valid n t)
    (h : orientation n s = orientation n t) {a b : Nat}
    (ha : a < n) (hb : b < n) (hab : cycleAdjacent n a b = true) :
    (placement s).idxOf a < (placement s).idxOf b ↔
      (placement t).idxOf a < (placement t).idxOf b := by
  by_cases heq : a = b
  · subst b; simp
  have hneS := (List.idxOf_inj (hs.placement_mem.mpr ha)).not.mpr heq
  have hneT := (List.idxOf_inj (ht.placement_mem.mpr ha)).not.mpr heq
  simp only [cycleAdjacent, Bool.or_eq_true, beq_iff_eq] at hab
  rcases hab with hab | hab
  · simpa [hab] using orientation_edge_iff h ha
  · have hr : (placement s).idxOf b < (placement s).idxOf a ↔
        (placement t).idxOf b < (placement t).idxOf a := by
      simpa [hab] using orientation_edge_iff h hb
    omega

def exchange (s : State) : State := (s.2, s.1)

theorem exchange_exchange (s : State) : exchange (exchange s) = s := rfl

theorem placement_exchange (s : State) : placement (exchange s) = (placement s).reverse := by
  simp [placement, exchange]

theorem Valid.exchange {n : Nat} {s : State} (hs : Valid n s) : Valid n (exchange s) :=
  List.perm_append_comm.trans hs

theorem transition_exchange {adj : Nat → Nat → Bool} {budget pos : Nat}
    {s t : State} {side : Bool} {initiating : Nat}
    (h : transition adj budget s side pos = some (t, initiating)) :
    transition adj budget (exchange s) (!side) pos = some (exchange t, initiating) := by
  cases side with
  | false =>
    cases he : complete adj budget s.1 pos with
    | none => simp [transition, he] at h
    | some result =>
      obtain ⟨r, d, i⟩ := result
      simp [transition, he] at h
      rcases h with ⟨rfl, rfl⟩
      simp [transition, exchange, he]

  | true =>
    cases he : complete adj budget s.2 pos with
    | none => simp [transition, he] at h
    | some result =>
      obtain ⟨r, d, i⟩ := result
      simp [transition, he] at h
      rcases h with ⟨rfl, rfl⟩
      simp [transition, exchange, he]

theorem before_of_reverse_before {q : Queue} (hnd : q.Nodup) {a b : Nat}
    (ha : a ∈ q) (hb : b ∈ q)
    (h : q.reverse.idxOf a < q.reverse.idxOf b) : q.idxOf b < q.idxOf a := by
  have hr : q.reverse.Pairwise (fun x y => q.idxOf y < q.idxOf x) := by
    rw [List.pairwise_reverse]
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [hnd.idxOf_getElem i hi, hnd.idxOf_getElem j hj] using hij
  have hh := List.pairwise_iff_getElem.mp hr (q.reverse.idxOf a) (q.reverse.idxOf b)
    (List.idxOf_lt_length_of_mem (by simpa using ha))
    (List.idxOf_lt_length_of_mem (by simpa using hb)) h
  simpa using hh

theorem idxOf_reverse_lt_iff {q : Queue} (hnd : q.Nodup) {a b : Nat}
    (ha : a ∈ q) (hb : b ∈ q) :
    q.reverse.idxOf a < q.reverse.idxOf b ↔ q.idxOf b < q.idxOf a := by
  constructor
  · exact before_of_reverse_before hnd ha hb
  · intro h
    exact before_of_reverse_before (by simpa using hnd) (by simpa using hb) (by simpa using ha)
      (by simpa using h)

theorem orientation_eq_of_except {n p v : Nat} {s t : State} (hn : 0 < n)
    (hpv : ((placement s).idxOf p < (placement s).idxOf v) ↔
      ((placement t).idxOf p < (placement t).idxOf v))
    (hvp : ((placement s).idxOf v < (placement s).idxOf p) ↔
      ((placement t).idxOf v < (placement t).idxOf p))
    (hrest : ∀ a b, a < n → b < n → cycleAdjacent n a b = true →
      ¬ ((a = p ∧ b = v) ∨ (a = v ∧ b = p)) →
      ((placement s).idxOf a < (placement s).idxOf b ↔
        (placement t).idxOf a < (placement t).idxOf b)) :
    orientation n s = orientation n t := by
  have hall (a b : Nat) (ha : a < n) (hb : b < n) (hab : cycleAdjacent n a b = true) :
      (placement s).idxOf a < (placement s).idxOf b ↔
        (placement t).idxOf a < (placement t).idxOf b := by
    by_cases hex : (a = p ∧ b = v) ∨ (a = v ∧ b = p)
    · rcases hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hpv
      · exact hvp
    · exact hrest a b ha hb hab hex
  apply List.map_congr_left
  intro a ha
  simp only [hall a ((a + 1) % n) (List.mem_range.mp ha) (Nat.mod_lt _ hn)
    (by simp [cycleAdjacent])]

theorem orientation_exchange_eq {n : Nat} {s t : State} (hn : 0 < n)
    (hs : Valid n s) (ht : Valid n t) (h : orientation n s = orientation n t) :
    orientation n (exchange s) = orientation n (exchange t) := by
  apply List.map_congr_left
  intro a ha
  have ha' := List.mem_range.mp ha
  have hb' : (a + 1) % n < n := Nat.mod_lt _ hn
  have hh := orientation_before_iff hs ht h hb' ha'
    (by simp [cycleAdjacent])
  simp only [placement_exchange,
    idxOf_reverse_lt_iff hs.placement_nodup (hs.placement_mem.mpr ha') (hs.placement_mem.mpr hb'),
    idxOf_reverse_lt_iff ht.placement_nodup (ht.placement_mem.mpr ha') (ht.placement_mem.mpr hb'), hh]

end OddCycle
