import OddCycle.IncomingDifference
import OddCycle.UnitTargetCounts
import OddCycle.ShortOIStationary

/-! The complete lost-event list for the unit-rate target: one event for
each insertion position before the first tail-block label. -/

namespace OddCycle

theorem first_singleton_budget_stable {adj : Nat → Nat → Bool} {w v budget pos init d : Nat}
    {source : State} {rest : Queue} (hw : 1 ≤ w) (hv : 1 ≤ v)
    (he : transition adj budget source false pos = some (([d], rest), init)) :
    transition adj w source false pos = transition adj v source false pos := by
  cases hc : complete adj budget source.1 pos with
  | none => simp [transition, hc] at he
  | some result =>
    obtain ⟨out, departed, initiating⟩ := result
    simp [transition, hc] at he
    have hout : out = [d] := he.1.1
    have hlen : source.1.length = 2 := by
      have hh := (complete_population hc).length_eq
      simp only [hout, List.length_append, List.length_singleton] at hh
      omega
    have bound (b : Nat) (hb : 1 ≤ b) : PathsBounded adj b source.1 := by
      intro q hq _
      have hh := hq.length_le
      omega
    have hh := complete_short_budgets (bound w hw) (bound v hv) pos
    simp only [transition, Bool.false_eq_true, if_false, hh]

theorem second_singleton_complete {adj : Nat → Nat → Bool} {budget pos init d : Nat}
    {source : State} {rest : Queue}
    (he : transition adj budget source true pos = some (([d], rest), init)) :
    source.1 = [] ∧ complete adj budget source.2 pos = some (rest, d, init) := by
  cases hc : complete adj budget source.2 pos with
  | none => simp [transition, hc] at he
  | some result =>
    obtain ⟨out, departed, initiating⟩ := result
    simp [transition, hc] at he
    obtain ⟨⟨hfirst, hout⟩, hi⟩ := he
    have hlen := congrArg List.length hfirst
    simp only [List.length_append, List.length_singleton] at hlen
    have hempty : source.1 = [] := List.length_eq_zero_iff.mp (by omega)
    have hd : departed = d := by simpa only [hempty, List.nil_append, List.singleton_inj] using hfirst
    simp only [hempty, hout, hd, hi, and_self]

theorem unit_lost_predecessors {n w : Nat} {states : List State} (hw : 1 ≤ w)
    (hn : 2 * w + 1 < n) (hs : OrientationSupport n states) (P : Queue)
    (hP : ∀ x ∈ P, 2 * w + 2 ≤ x ∧ x < n)
    (ht : ([0], P ++ unitTargetTail w) ∈ states) :
    (gainedOccurrences (cycleAdjacent n) n w states ([0], P ++ unitTargetTail w)).Perm
      ((List.range (P.length + 1)).map
        (backwardOccurrence (cycleAdjacent n) (P ++ unitTargetTail w) [] 0 true)) := by
  let rest := P ++ unitTargetTail w
  have hvalid := hs.valid _ ht
  have hnd : (rest ++ [0]).Nodup := by
    have hh := hvalid.exchange
    exact hh.nodup_iff.mpr List.nodup_range
  have hpbound {p : Nat} (hp : p ≤ P.length) : p ≤ rest.length := by
    dsimp only [rest]
    simp only [List.length_append]
    omega
  have hm (o : Occurrence) :
      o ∈ gainedOccurrences (cycleAdjacent n) n w states ([0], rest) ↔
        o ∈ (List.range (P.length + 1)).map (backwardOccurrence (cycleAdjacent n) rest [] 0 true) := by
    rw [mem_gainedOccurrences]
    constructor
    · rintro ⟨ho, he, hnot⟩
      have hside : o.side = true := by
        cases hh : o.side with
        | true => rfl
        | false =>
          have hefalse := he
          rw [hh] at hefalse
          have hstable := first_singleton_budget_stable hw (by omega : 1 ≤ n) hefalse
          exact False.elim (hnot (by rw [hh]; exact hstable.trans hefalse))
      have he' := he
      rw [hside] at he'
      obtain ⟨hq, hp, hi⟩ := unlimited_first_predecessor (rest := rest) (other := []) (d := 0)
        (hs.valid _ ho).exchange (transition_exchange he')
      have hq' := congrArg exchange hq
      change o.source = ([], reverseInput (cycleAdjacent n) rest 0 o.pos) at hq'
      have hcompnot : complete (cycleAdjacent n) w (reverseInput (cycleAdjacent n) rest 0 o.pos) o.pos ≠
          some (rest, 0, (unlimitedCarry (cycleAdjacent n) 0 (rest.drop o.pos).reverse).2) := by
        intro hc
        apply hnot
        simp only [hq', hside, hi, transition, if_true, hc, List.nil_append]
        rfl
      have hcount : w < replacementCount (cycleAdjacent n) 0 (rest.drop o.pos).reverse := by
        exact Nat.lt_of_not_ge (fun hle => hcompnot ((reverseInput_limited_iff (cycleAdjacent_symm n) hnd hp).mpr hle))
      have hpP := (unitTarget_backward_count (by omega) hn P hP o.pos).mp hcount
      exact List.mem_map.mpr ⟨o.pos, List.mem_range.mpr (by omega), by
        cases o
        simp_all only [backwardOccurrence, if_true]⟩
    · intro ho
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
      have hpP : p ≤ P.length := by have := List.mem_range.mp hp; omega
      have hpp := hpbound hpP
      refine ⟨backward_member hs (by omega) true ht hpp, backward_transition true hvalid hpp, ?_⟩
      intro he
      have hh := (second_singleton_complete he).2
      have hcount := (reverseInput_limited_iff (cycleAdjacent_symm n) hnd hpp).mp hh
      have hgt := (unitTarget_backward_count (by omega) hn P hP p).mpr hpP
      exact Nat.not_lt_of_ge hcount hgt
  apply (List.perm_ext_iff_of_nodup (gainedOccurrences_nodup hs.nodup _)
    (List.nodup_range.map (fun a b h => congrArg Occurrence.pos h))).mpr
  exact hm

end OddCycle
