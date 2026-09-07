import OddCycle.Model

namespace OddCycle

def rotate (n source k : Nat) : Nat := (source + k) % n
def unrotate (n source k : Nat) : Nat := (n - source + k) % n
def reflect (n k : Nat) : Nat := (n - k) % n

theorem unrotate_rotate {n source k : Nat} (hs : source < n) (hk : k < n) :
    unrotate n source (rotate n source k) = k := by
  unfold unrotate rotate
  rw [Nat.add_mod_mod]
  rw [show n - source + (source + k) = n + k by omega]
  simp [Nat.mod_eq_of_lt hk]

theorem rotate_unrotate {n source k : Nat} (hs : source < n) (hk : k < n) :
    rotate n source (unrotate n source k) = k := by
  unfold unrotate rotate
  rw [Nat.add_mod_mod]
  rw [show source + (n - source + k) = n + k by omega]
  simp [Nat.mod_eq_of_lt hk]

theorem reflect_involutive {n k : Nat} (hk : k < n) : reflect n (reflect n k) = k := by
  by_cases hz : k = 0
  · subst k; simp [reflect]
  · have hl : n - k < n := by omega
    simp only [reflect, Nat.mod_eq_of_lt hl]
    rw [show n - (n - k) = k by omega, Nat.mod_eq_of_lt hk]

theorem cycleAdjacent_symm (n a b : Nat) : cycleAdjacent n a b = cycleAdjacent n b a := by
  simp [cycleAdjacent, Bool.or_comm]

theorem rotate_adj {n source a b : Nat} (h : cycleAdjacent n a b = true) :
    cycleAdjacent n (rotate n source a) (rotate n source b) = true := by
  have hstep (k : Nat) : (rotate n source k + 1) % n = rotate n source ((k + 1) % n) := by
    simp only [rotate, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
  simp only [cycleAdjacent, Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h with h | h
  · exact Or.inl ((hstep a).trans (congrArg (rotate n source) h))
  · exact Or.inr ((hstep b).trans (congrArg (rotate n source) h))

theorem rotate_adj_iff {n source a b : Nat} (hs : source < n) (ha : a < n) (hb : b < n) :
    cycleAdjacent n (rotate n source a) (rotate n source b) = true ↔
      cycleAdjacent n a b = true := by
  constructor
  · intro h
    have hh := rotate_adj (source := n - source) h
    change cycleAdjacent n (unrotate n source (rotate n source a))
      (unrotate n source (rotate n source b)) = true at hh
    simpa [unrotate_rotate hs ha, unrotate_rotate hs hb] using hh
  · exact rotate_adj

theorem cycleAdjacent_iff {n a b : Nat} (ha : a < n) (hb : b < n) :
    cycleAdjacent n a b = true ↔
      a + 1 = b ∨ b + 1 = a ∨ (a = 0 ∧ b + 1 = n) ∨ (b = 0 ∧ a + 1 = n) := by
  have hmod (k : Nat) (hk : k < n) :
      (k + 1) % n = if k + 1 = n then 0 else k + 1 := by
    split_ifs with h
    · simp [h]
    · apply Nat.mod_eq_of_lt; omega
  simp only [cycleAdjacent, Bool.or_eq_true, beq_iff_eq, hmod a ha, hmod b hb]
  split_ifs <;> omega

theorem reflect_adj_iff {n a b : Nat} (ha : a < n) (hb : b < n) :
    cycleAdjacent n (reflect n a) (reflect n b) = true ↔ cycleAdjacent n a b = true := by
  have hn : 0 < n := by omega
  have hfa : reflect n a < n := Nat.mod_lt _ hn
  have hfb : reflect n b < n := Nat.mod_lt _ hn
  rw [cycleAdjacent_iff hfa hfb, cycleAdjacent_iff ha hb]
  by_cases hza : a = 0 <;> by_cases hzb : b = 0
  · subst a; subst b; simp [reflect]
  · subst a
    have hl : n - b < n := by omega
    simp only [reflect, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt hl, true_and]
    omega
  · subst b
    have hl : n - a < n := by omega
    simp only [reflect, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt hl, true_and]
    omega
  · have hla : n - a < n := by omega
    have hlb : n - b < n := by omega
    simp only [reflect, Nat.mod_eq_of_lt hla, Nat.mod_eq_of_lt hlb]
    omega

end OddCycle
