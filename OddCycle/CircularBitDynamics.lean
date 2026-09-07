import OddCycle.CircularRunEncoding

/-! Homogeneous-block flips and their exact effect on circular runs. -/

namespace OddCycle.CircularWord

theorem circularRuns_encode_odd {b : Bool} {a c : Nat} {r : List Nat}
    (hpos : ∀ x ∈ a :: (r ++ [c]), 0 < x) (hodd : r.length % 2 = 1) :
    circularRuns (encode b (a :: (r ++ [c]))) = r ++ [c + a] := by
  rw [circularRuns, linearRuns_encode b _ hpos, List.headD_cons]
  have hword : (encode b (a :: (r ++ [c]))).rotate a = encode (!b) (r ++ [c + a]) := by
    change (List.replicate a b ++ encode (!b) (r ++ [c])).rotate a = _
    have hr := List.rotate_append_length_eq (List.replicate a b) (encode (!b) (r ++ [c]))
    simp only [List.length_replicate] at hr
    rw [hr, encode_append, encode_append, phase_odd (!b) hodd, Bool.not_not]
    simp only [encode, List.append_nil, List.append_assoc, ← List.replicate_add]
  rw [hword]
  apply linearRuns_encode
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hpos x (by simp [hx])
  · have ha := hpos a (by simp)
    have hc := hpos c (by simp)
    simp only [List.mem_singleton] at hx
    omega

theorem Nonconstant.perm {q z : List Bool} (h : Nonconstant q) (hp : q.Perm z) : Nonconstant z := by
  obtain ⟨a, ha, b, hb, hne⟩ := h
  exact ⟨a, hp.mem_iff.mp ha, b, hp.mem_iff.mp hb, hne⟩

theorem encode_nonconstant {b : Bool} {a c : Nat} {r : List Nat}
    (ha : 0 < a) (hc : 0 < c) : Nonconstant (encode b (a :: c :: r)) := by
  refine ⟨b, ?_, !b, ?_, by simp⟩
  · simp [encode, Nat.ne_of_gt ha]
  · simp [encode, Nat.ne_of_gt hc]

/-- Flipping the first bit of a sufficiently long initial block is either
a boundary donation or an interior split, according to the run at the other
end of the chosen circular cut. -/
theorem first_flip_run_reachable {w : Nat} {b : Bool} {tail : List Bool}
    (hw : 1 ≤ w) (hq : Nonconstant (List.replicate (w + 1) b ++ tail)) :
    CircularRun.Reach w
      (circularRuns (List.replicate (w + 1) b ++ tail))
      (circularRuns ((!b) :: (List.replicate w b ++ tail))) := by
  let q := List.replicate (w + 1) b ++ tail
  obtain ⟨a, c, r, hr⟩ := nonconstant_two_runs hq
  change linearRuns q = a :: c :: r at hr
  have hhead : q.headD false = b := by simp [q, List.replicate_succ]
  have hencode : q = encode b (a :: c :: r) := by
    simpa only [hr, hhead] using (encode_linearRuns q).symm
  have hpos : ∀ x ∈ a :: c :: r, 0 < x := by
    intro x hx
    exact linearRuns_positive q x (by simpa only [hr] using hx)
  have ha : w + 1 ≤ a := by
    have hh := replicate_prefix_le_head b (w + 1) tail (by omega)
    change w + 1 ≤ (linearRuns q).headD 0 at hh
    simpa only [hr, List.headD_cons] using hh
  have htail : (!b) :: (List.replicate w b ++ tail) = encode (!b) (1 :: (a - 1) :: c :: r) := by
    have he : b :: (List.replicate w b ++ tail) =
        b :: (List.replicate (a - 1) b ++ encode (!b) (c :: r)) := by
      have ha' : a = (a - 1) + 1 := by omega
      have hh : List.replicate (w + 1) b ++ tail =
          List.replicate a b ++ encode (!b) (c :: r) := hencode
      rw [ha'] at hh
      simpa only [List.replicate_succ, List.cons_append] using hh
    have hh := (List.cons.inj he).2
    simpa only [encode, List.replicate_one, List.singleton_append, Bool.not_not] using
      congrArg (Bool.not b :: ·) hh
  have htpos : ∀ x ∈ 1 :: (a - 1) :: c :: r, 0 < x := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · omega
    · omega
    · exact hpos x (by simp only [List.mem_cons]; tauto)
  obtain ⟨pre, last, hlast⟩ : ∃ pre last, c :: r = pre ++ [last] := by
    exact ⟨(c :: r).dropLast, (c :: r).getLast (by simp),
      (List.dropLast_append_getLast (by simp)).symm⟩
  have hp : ∀ x ∈ a :: (pre ++ [last]), 0 < x := by simpa only [← hlast] using hpos
  have ht : ∀ x ∈ 1 :: (a - 1) :: (pre ++ [last]), 0 < x := by simpa only [← hlast] using htpos
  change CircularRun.Reach w (circularRuns q) (circularRuns ((!b) :: (List.replicate w b ++ tail)))
  rw [hencode, htail, hlast]
  by_cases heven : pre.length % 2 = 0
  · have he : Even (a :: (pre ++ [last])).length := by
      rw [Nat.even_iff]
      simp [heven, Nat.add_mod]
    rw [circularRuns_encode hp he]
    have ho : ((a - 1) :: pre).length % 2 = 1 := by simp [Nat.add_mod, heven]
    have htarget := circularRuns_encode_odd (b := !b) (a := 1) (c := last) (r := (a - 1) :: pre) ht ho
    simp only [List.cons_append] at htarget
    rw [htarget]
    have hs : CircularRun.Step w (pre ++ [last, a]) (pre ++ [last + 1, a - 1]) := by
      have hh := CircularRun.Step.take (w := w) pre [] last (a - 1) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ a)] using hh
    have hrot := CircularRun.Step.rotate (w := w) (pre ++ [last + 1]) [a - 1]
    apply (Relation.ReflTransGen.single (by simpa only [List.append_assoc] using hs)).trans
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
      Relation.ReflTransGen.single hrot
  · have ho : pre.length % 2 = 1 := by omega
    rw [circularRuns_encode_odd hp ho]
    have hev : Even (1 :: (a - 1) :: (pre ++ [last])).length := by
      rw [Nat.even_iff]
      simp [Nat.add_mod, ho]
    rw [circularRuns_encode ht hev]
    have hs : CircularRun.Step w (pre ++ [last + a]) (pre ++ [last, 1, a - 1]) := by
      have hh := CircularRun.Step.split (w := w) pre [] last (a - 1)
        (hp last (by simp)) (by omega) (Or.inr (by omega))
      have he : last + 1 + (a - 1) = last + a := by omega
      simpa only [he] using hh
    have hrot := CircularRun.Step.rotate (w := w) (pre ++ [last, 1]) [a - 1]
    apply (Relation.ReflTransGen.single hs).trans
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
      Relation.ReflTransGen.single hrot

end OddCycle.CircularWord

namespace OddCycle.CircularRun

theorem Step.positive {w : Nat} {r s : List Nat} (hw : 1 ≤ w) (h : Step w r s)
    (hp : ∀ a ∈ r, 0 < a) : ∀ a ∈ s, 0 < a := by
  cases h with
  | rotate p q => simpa only [List.mem_append, or_comm] using hp
  | give p q a b ha =>
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | rfl | hx
    · exact hp x (by simp [hx])
    · omega
    · omega
    · exact hp x (by simp [hx])
  | take p q a b hb =>
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | rfl | hx
    · exact hp x (by simp [hx])
    · omega
    · omega
    · exact hp x (by simp [hx])
  | split p q a b ha hb _ =>
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | rfl | rfl | hx
    · exact hp x (by simp [hx])
    · exact ha
    · omega
    · exact hb
    · exact hp x (by simp [hx])

theorem Step.even {w : Nat} {r s : List Nat} (h : Step w r s) (he : Even r.length) : Even s.length := by
  rw [Nat.even_iff] at he ⊢
  cases h <;> simp only [List.length_append, List.length_cons] at he ⊢ <;> omega

theorem Reach.positive {w : Nat} {r s : List Nat} (hw : 1 ≤ w) (h : Reach w r s)
    (hp : ∀ a ∈ r, 0 < a) : ∀ a ∈ s, 0 < a := by
  induction h with
  | refl => exact hp
  | tail _ hs ih => exact hs.positive hw ih

theorem Reach.even {w : Nat} {r s : List Nat} (h : Reach w r s) (he : Even r.length) : Even s.length := by
  induction h with
  | refl => exact he
  | tail _ hs ih => exact hs.even ih

end OddCycle.CircularRun



namespace OddCycle.CircularRun

theorem Step.reverse {w : Nat} {r s : List Nat} (h : Step w r s) : Step w r.reverse s.reverse := by
  cases h with
  | rotate p q => simpa only [List.reverse_append] using Step.rotate q.reverse p.reverse
  | give p q a b ha =>
    simpa only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.cons_append] using Step.take q.reverse p.reverse b a ha
  | take p q a b hb =>
    simpa only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.cons_append] using Step.give q.reverse p.reverse b a hb
  | split p q a b ha hb hw =>
    have he : a + 1 + b = b + 1 + a := by omega
    simpa only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append,
      List.cons_append, he] using Step.split q.reverse p.reverse b a hb ha hw.symm

theorem Reach.reverse {w : Nat} {r s : List Nat} (h : Reach w r s) : Reach w r.reverse s.reverse :=
  Relation.ReflTransGen.lift List.reverse (fun _ _ hs => hs.reverse) h

end OddCycle.CircularRun

namespace OddCycle.CircularWord

theorem circularRuns_reverse_rotated {q : List Bool} (hq : Nonconstant q) :
    List.IsRotated (circularRuns q.reverse) (circularRuns q).reverse := by
  obtain ⟨b, hb⟩ := circular_encoding_rotated q
  have hh := hb.reverse
  rw [encode_reverse] at hh
  obtain ⟨k, hk⟩ := hh
  rw [← hk]
  apply circularRuns_rotate_encode
  · simpa using circularRuns_nonempty hq
  · intro a ha
    exact circularRuns_positive q a (by simpa using ha)
  · simpa using circularRuns_even hq

theorem first_flip_nonconstant {w : Nat} {b : Bool} {tail : List Bool} (hw : 1 ≤ w)
    :
    Nonconstant ((!b) :: (List.replicate w b ++ tail)) := by
  refine ⟨!b, by simp, b, ?_, by simp⟩
  simp [Nat.ne_of_gt (show 0 < w by omega)]

theorem last_flip_run_reachable {w : Nat} {b : Bool} {tail : List Bool}
    (hw : 1 ≤ w) (hq : Nonconstant (tail ++ List.replicate (w + 1) b)) :
    CircularRun.Reach w (circularRuns (tail ++ List.replicate (w + 1) b))
      (circularRuns ((tail ++ List.replicate w b) ++ [!b])) := by
  let q := tail ++ List.replicate (w + 1) b
  let z := (tail ++ List.replicate w b) ++ [!b]
  have hqr : Nonconstant q.reverse := hq.perm (List.reverse_perm q).symm
  have hf : Nonconstant (List.replicate (w + 1) b ++ tail.reverse) := by
    simpa only [q, List.reverse_append, List.reverse_replicate] using hqr
  have hzr : Nonconstant z.reverse := by
    simpa only [z, List.reverse_append, List.reverse_replicate, List.reverse_singleton,
      List.singleton_append] using first_flip_nonconstant (tail := tail.reverse) (b := b) hw
  have hz : Nonconstant z := hzr.perm (List.reverse_perm z)
  have hstep : CircularRun.Reach w (circularRuns q.reverse) (circularRuns z.reverse) := by
    simpa only [q, z, List.reverse_append, List.reverse_replicate, List.reverse_singleton,
      List.singleton_append] using first_flip_run_reachable hw hf
  have hqrot := (circularRuns_reverse_rotated hq).reverse
  have hzrot := (circularRuns_reverse_rotated hz).reverse
  have hs := (CircularRun.Reach.of_isRotated hqrot.symm).trans
    (hstep.reverse.trans (CircularRun.Reach.of_isRotated hzrot))
  simpa only [List.reverse_reverse] using hs

inductive LinearFlip (w : Nat) : List Bool → List Bool → Prop
  | first (pre post : List Bool) (b : Bool) :
      LinearFlip w (pre ++ List.replicate (w + 1) b ++ post)
        (pre ++ (!b) :: (List.replicate w b ++ post))
  | last (pre post : List Bool) (b : Bool) :
      LinearFlip w (pre ++ List.replicate (w + 1) b ++ post)
        (pre ++ List.replicate w b ++ (!b) :: post)

theorem LinearFlip.length_eq {w : Nat} {q z : List Bool} (h : LinearFlip w q z) : q.length = z.length := by
  cases h <;> simp <;> omega

theorem LinearFlip.nonconstant {w : Nat} {q z : List Bool} (hw : 1 ≤ w) (h : LinearFlip w q z) :
    Nonconstant z := by
  cases h with
  | first pre post b =>
    exact ⟨!b, by simp, b, by simp [Nat.ne_of_gt (show 0 < w by omega)], by simp⟩
  | last pre post b =>
    exact ⟨!b, by simp, b, by simp [Nat.ne_of_gt (show 0 < w by omega)], by simp⟩

theorem first_context_run_reachable {w : Nat} (pre post : List Bool) (b : Bool)
    (hw : 1 ≤ w) (hq : Nonconstant (pre ++ List.replicate (w + 1) b ++ post)) :
    CircularRun.Reach w (circularRuns (pre ++ List.replicate (w + 1) b ++ post))
      (circularRuns (pre ++ (!b) :: (List.replicate w b ++ post))) := by
  have hqrot : List.IsRotated (pre ++ List.replicate (w + 1) b ++ post)
      (List.replicate (w + 1) b ++ (post ++ pre)) := by
    refine ⟨pre.length, ?_⟩
    simpa only [List.append_assoc] using
      List.rotate_append_length_eq pre (List.replicate (w + 1) b ++ post)
  have hzrot : List.IsRotated (pre ++ (!b) :: (List.replicate w b ++ post))
      ((!b) :: (List.replicate w b ++ (post ++ pre))) := by
    refine ⟨pre.length, ?_⟩
    simpa only [List.append_assoc, List.cons_append] using
      List.rotate_append_length_eq pre ((!b) :: (List.replicate w b ++ post))
  have hz := (LinearFlip.first (w := w) pre post b).nonconstant hw
  exact (CircularRun.Reach.of_isRotated (circularRuns_isRotated hq hqrot).symm).trans
    ((first_flip_run_reachable hw (hq.perm hqrot.perm)).trans
      (CircularRun.Reach.of_isRotated (circularRuns_isRotated hz hzrot)))

theorem run_reachable_of_reverse {w : Nat} {q z : List Bool}
    (hq : Nonconstant q) (hz : Nonconstant z)
    (h : CircularRun.Reach w (circularRuns q.reverse) (circularRuns z.reverse)) :
    CircularRun.Reach w (circularRuns q) (circularRuns z) := by
  have hqrot := (circularRuns_reverse_rotated hq).reverse
  have hzrot := (circularRuns_reverse_rotated hz).reverse
  have hs := (CircularRun.Reach.of_isRotated hqrot.symm).trans
    (h.reverse.trans (CircularRun.Reach.of_isRotated hzrot))
  simpa only [List.reverse_reverse] using hs

theorem LinearFlip.run_reachable {w : Nat} {q z : List Bool} (hw : 1 ≤ w)
    (hq : Nonconstant q) (h : LinearFlip w q z) :
    CircularRun.Reach w (circularRuns q) (circularRuns z) := by
  cases h with
  | first pre post b => exact first_context_run_reachable pre post b hw hq
  | last pre post b =>
    apply run_reachable_of_reverse hq ((LinearFlip.last pre post b).nonconstant hw)
    have hqr := hq.perm (List.reverse_perm _).symm
    have hh := first_context_run_reachable post.reverse pre.reverse b hw
      (by simpa only [List.reverse_append, List.reverse_replicate, List.append_assoc] using hqr)
    simpa only [List.reverse_append, List.reverse_replicate, List.reverse_cons,
      List.append_assoc, List.singleton_append] using hh

def CircularFlip (w : Nat) (q z : List Bool) : Prop :=
  ∃ k, LinearFlip w (q.rotate k) (z.rotate k)

theorem CircularFlip.nonconstant {w : Nat} {q z : List Bool} (hw : 1 ≤ w) (h : CircularFlip w q z) :
    Nonconstant z := by
  obtain ⟨k, hk⟩ := h
  exact (hk.nonconstant hw).perm (List.rotate_perm z k)

theorem CircularFlip.run_reachable {w : Nat} {q z : List Bool} (hw : 1 ≤ w)
    (hq : Nonconstant q) (h : CircularFlip w q z) :
    CircularRun.Reach w (circularRuns q) (circularRuns z) := by
  obtain ⟨k, hk⟩ := h
  have hr := hk.run_reachable hw (hq.perm (List.rotate_perm q k).symm)
  have hz := (hk.nonconstant hw).perm (List.rotate_perm z k)
  exact (CircularRun.Reach.of_isRotated (circularRuns_isRotated hq ⟨k, rfl⟩).symm).trans
    (hr.trans (CircularRun.Reach.of_isRotated (circularRuns_isRotated hz ⟨k, rfl⟩)))

theorem encode_not (b : Bool) (r : List Nat) : (encode b r).map Bool.not = encode (!b) r := by
  induction r generalizing b with
  | nil => rfl
  | cons a r ih => simp [encode, ih]

theorem replicate_blocks (a k : Nat) (b : Bool) (q : List Bool) :
    List.replicate a b ++ (List.replicate k b ++ q) = List.replicate (a + k) b ++ q := by
  rw [← List.append_assoc, ← List.replicate_add]

theorem cons_replicate_block (a : Nat) (b : Bool) (q : List Bool) :
    b :: (List.replicate a b ++ q) = List.replicate (a + 1) b ++ q := by
  simp only [List.replicate_succ, List.cons_append]

theorem replicate_cons_block (a : Nat) (b : Bool) (q : List Bool) :
    List.replicate a b ++ b :: q = List.replicate (a + 1) b ++ q := by
  rw [List.replicate_succ']
  simp only [List.append_assoc, List.singleton_append]

theorem give_is_linearFlip {w a b : Nat} (pre post : List Nat) (bit : Bool) (ha : w ≤ a) :
    LinearFlip w (encode bit (pre ++ (a + 1) :: b :: post))
      (encode bit (pre ++ a :: (b + 1) :: post)) := by
  let c := phase bit pre.length
  have hh := LinearFlip.last (w := w) (encode bit pre ++ List.replicate (a - w) c)
    (List.replicate b (!c) ++ encode c post) c
  have he : a - w + (w + 1) = a + 1 := by omega
  simpa only [encode_append, encode, Bool.not_not, List.append_assoc, c,
    replicate_blocks, cons_replicate_block, Nat.sub_add_cancel ha, he] using hh

theorem take_is_linearFlip {w a b : Nat} (pre post : List Nat) (bit : Bool) (hb : w ≤ b) :
    LinearFlip w (encode bit (pre ++ a :: (b + 1) :: post))
      (encode bit (pre ++ (a + 1) :: b :: post)) := by
  let c := phase bit pre.length
  have hh := LinearFlip.first (w := w) (encode bit pre ++ List.replicate a c)
    (List.replicate (b - w) (!c) ++ encode c post) (!c)
  have he : w + 1 + (b - w) = b + 1 := by omega
  have he' : w + (b - w) = b := by omega
  simpa only [encode_append, encode, Bool.not_not, List.append_assoc, c,
    replicate_blocks, replicate_cons_block, he, he'] using hh

theorem split_is_linearFlip {w a b : Nat} (pre post : List Nat) (bit : Bool) (hw : w ≤ a ∨ w ≤ b) :
    LinearFlip w (encode bit (pre ++ (a + 1 + b) :: post))
      (encode bit (pre ++ a :: 1 :: b :: post)) := by
  let c := phase bit pre.length
  rcases hw with ha | hb
  · have hh := LinearFlip.last (w := w) (encode bit pre ++ List.replicate (a - w) c)
      (List.replicate b c ++ encode (!c) post) c
    have he : a - w + (w + 1 + b) = a + 1 + b := by omega
    simpa only [encode_append, encode, Bool.not_not, List.append_assoc, c,
      replicate_blocks, Nat.sub_add_cancel ha, List.replicate_one, List.singleton_append, he] using hh
  · have hh := LinearFlip.first (w := w) (encode bit pre ++ List.replicate a c)
      (List.replicate (b - w) c ++ encode (!c) post) c
    have he : a + (w + 1 + (b - w)) = a + 1 + b := by omega
    have he' : w + (b - w) = b := by omega
    simpa only [encode_append, encode, Bool.not_not, List.append_assoc, c,
      replicate_blocks, List.replicate_one, List.singleton_append, he, he'] using hh

end OddCycle.CircularWord

namespace OddCycle.CircularWord

/-- Adding changes of circular cut and global bit complementation. This
auxiliary relation will be compared with the original flip graph using its
finite graph symmetries; these extra edges are not queue completions. -/
inductive AugmentedStep (w : Nat) : List Bool → List Bool → Prop
  | flip {q z : List Bool} (h : LinearFlip w q z) : AugmentedStep w q z
  | rotate {q z : List Bool} (h : List.IsRotated q z) : AugmentedStep w q z
  | negate (q : List Bool) : AugmentedStep w q (q.map Bool.not)

abbrev AugmentedReach (w : Nat) := Relation.ReflTransGen (AugmentedStep w)

theorem AugmentedStep.nonconstant {w : Nat} {q z : List Bool} (hw : 1 ≤ w)
    (hq : Nonconstant q) (h : AugmentedStep w q z) : Nonconstant z := by
  cases h with
  | flip hf => exact hf.nonconstant hw
  | rotate hr => exact hq.perm hr.perm
  | negate =>
    obtain ⟨a, ha, b, hb, hne⟩ := hq
    exact ⟨!a, List.mem_map.mpr ⟨a, ha, rfl⟩, !b, List.mem_map.mpr ⟨b, hb, rfl⟩, by simpa using hne⟩

theorem AugmentedStep.run_reachable {w : Nat} {q z : List Bool} (hw : 1 ≤ w)
    (hq : Nonconstant q) (h : AugmentedStep w q z) :
    CircularRun.Reach w (circularRuns q) (circularRuns z) := by
  cases h with
  | flip hf => exact hf.run_reachable hw hq
  | rotate hr => exact CircularRun.Reach.of_isRotated (circularRuns_isRotated hq hr).symm
  | negate => rw [circularRuns_not]

theorem AugmentedReach.project {w : Nat} {q z : List Bool} (hw : 1 ≤ w)
    (hq : Nonconstant q) (h : AugmentedReach w q z) :
    Nonconstant z ∧ CircularRun.Reach w (circularRuns q) (circularRuns z) := by
  induction h with
  | refl => exact ⟨hq, .refl⟩
  | tail _ hs ih => exact ⟨hs.nonconstant hw ih.1, ih.2.trans (hs.run_reachable hw ih.1)⟩

theorem change_start_bit (w : Nat) (r : List Nat) (b c : Bool) :
    AugmentedReach w (encode b r) (encode c r) := by
  by_cases he : b = c
  · subst c; exact .refl
  · have hc : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    have hh := AugmentedStep.negate (w := w) (encode b r)
    simpa only [encode_not] using Relation.ReflTransGen.single hh

theorem run_step_lifts {w : Nat} {r s : List Nat} (h : CircularRun.Step w r s)
    (heven : Even r.length) (bit : Bool) : AugmentedReach w (encode bit r) (encode bit s) := by
  cases h with
  | rotate p q =>
    let c := phase bit p.length
    have hc : phase c q.length = bit := by
      rw [Nat.even_iff, List.length_append] at heven
      change phase (phase bit p.length) q.length = bit
      rw [← phase_add]
      simp only [phase, heven, if_true]
    have hrot : List.IsRotated (encode bit (p ++ q)) (encode c (q ++ p)) := by
      refine ⟨(encode bit p).length, ?_⟩
      rw [encode_append, encode_append, hc]
      exact List.rotate_append_length_eq _ _
    exact (Relation.ReflTransGen.single (AugmentedStep.rotate hrot)).trans
      (change_start_bit w (q ++ p) c bit)
  | give p q a b ha => exact .single (.flip (give_is_linearFlip p q bit ha))
  | take p q a b hb => exact .single (.flip (take_is_linearFlip p q bit hb))
  | split p q a b _ _ hw => exact .single (.flip (split_is_linearFlip p q bit hw))

theorem run_reach_lifts {w : Nat} {r s : List Nat} (h : CircularRun.Reach w r s)
    (heven : Even r.length) (bit : Bool) : AugmentedReach w (encode bit r) (encode bit s) := by
  induction h with
  | refl => exact .refl
  | tail hp hs ih => exact ih.trans (run_step_lifts hs (CircularRun.Reach.even hp heven) bit)

theorem augmentedReach_iff_runs {w : Nat} {q z : List Bool}
    (hw : 1 ≤ w) (hq : Nonconstant q) :
    AugmentedReach w q z ↔ CircularRun.Reach w (circularRuns q) (circularRuns z) := by
  constructor
  · exact fun h => (h.project hw hq).2
  · intro h
    obtain ⟨b, hb⟩ := circular_encoding_rotated q
    obtain ⟨c, hc⟩ := circular_encoding_rotated z
    exact (Relation.ReflTransGen.single (AugmentedStep.rotate hb.symm)).trans
      ((run_reach_lifts h (circularRuns_even hq) b).trans
        ((change_start_bit w (circularRuns z) b c).trans
          (Relation.ReflTransGen.single (AugmentedStep.rotate hc))))

theorem augmented_terminal_iff_run_terminal {w : Nat} {q : List Bool}
    (hw : 1 ≤ w) (hq : Nonconstant q) :
    OddCycle.ReachabilityQuotient.Terminal (AugmentedStep w) q ↔
      CircularRun.Terminal w (circularRuns q) := by
  constructor
  · intro ht r hr
    obtain ⟨b, hb⟩ := circular_encoding_rotated q
    have hforward : AugmentedReach w q (encode b r) :=
      (Relation.ReflTransGen.single (AugmentedStep.rotate hb.symm)).trans
        (run_reach_lifts hr (circularRuns_even hq) b)
    have hnc := (hforward.project hw hq).1
    have hback := (AugmentedReach.project hw hnc (ht (encode b r) hforward)).2
    have hpos := CircularRun.Reach.positive hw hr (circularRuns_positive q)
    have heven := CircularRun.Reach.even hr (circularRuns_even hq)
    have hne : r ≠ [] := by
      have hh := CircularRun.Reach.length_le hr
      have hp := List.length_pos_iff.mpr (circularRuns_nonempty hq)
      intro he
      simp only [he, List.length_nil] at hh
      omega
    have hrot := circularRuns_rotate_encode 0 b r hne hpos heven
    simp only [List.rotate_zero] at hrot
    exact (CircularRun.Reach.of_isRotated hrot.symm).trans hback
  · intro ht z hz
    have hh := AugmentedReach.project hw hq hz
    exact (augmentedReach_iff_runs hw hh.1).mpr (ht (circularRuns z) hh.2)

theorem augmented_terminal_iff {w : Nat} {q : List Bool}
    (hw : 1 ≤ w) (hq : Nonconstant q) :
    OddCycle.ReachabilityQuotient.Terminal (AugmentedStep w) q ↔
      CircularRun.Short w (circularRuns q) ∨ CircularRun.Exceptional w (circularRuns q) := by
  rw [augmented_terminal_iff_run_terminal hw hq, CircularRun.terminal_iff hw]

end OddCycle.CircularWord
