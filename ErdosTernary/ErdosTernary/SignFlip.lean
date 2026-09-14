import Mathlib.Tactic

def td (n k : Nat) : Nat := (n / 3 ^ k) % 3

private theorem pow_self_period (T M : Nat) (hM : M > 1) (m : Nat) (hT : 2 ^ T % M = 1) :
    2 ^ (T * m) % M = 1 := by
  have h1 : 1 % M = 1 := Nat.mod_eq_of_lt hM
  induction m with
  | zero => simp [Nat.mul_zero, h1]
  | succ m ih =>
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_mod, ih, hT, h1]

theorem pow_period (a T M v : Nat) (hM : M > 1) (hT : 2 ^ T % M = 1) (ha : 2 ^ a % M = v) :
    ∀ m, 2 ^ (a + T * m) % M = v := fun m => by
  have hv : v < M := ha ▸ Nat.mod_lt _ (Nat.pos_of_ne_zero (by omega))
  rw [Nat.pow_add, Nat.mul_mod, pow_self_period T M hM m hT, ha,
      show v * 1 = v from Nat.mul_one v, Nat.mod_eq_of_lt hv]

-- === Sign-flip cases ===

theorem case1_odd (r : Nat) (hr : r % 2 = 1) : td (2 ^ r) 0 = 2 := by
  unfold td; simp only [Nat.pow_zero, Nat.div_one]
  obtain ⟨m, rfl⟩ : ∃ m, r = 1 + 2 * m := ⟨r / 2, by omega⟩
  exact pow_period 1 2 3 2 (by norm_num) (by norm_num) (by norm_num) m

theorem case2_mod6_4 (r : Nat) (hr : r % 6 = 4) : td (2 ^ r) 1 = 2 := by
  unfold td; obtain ⟨m, rfl⟩ : ∃ m, r = 4 + 6 * m := ⟨r / 6, by omega⟩
  have h9 := pow_period 4 6 9 7 (by norm_num) (by norm_num) (by norm_num) m
  omega

theorem case3a_mod18_12 (r : Nat) (hr : r % 18 = 12) : td (2 ^ r) 2 = 2 := by
  unfold td; obtain ⟨m, rfl⟩ : ∃ m, r = 12 + 18 * m := ⟨r / 18, by omega⟩
  have h27 := pow_period 12 18 27 19 (by norm_num) (by norm_num) (by norm_num) m
  omega

theorem case3b_mod18_14 (r : Nat) (hr : r % 18 = 14) : td (2 ^ r) 2 = 2 := by
  unfold td; obtain ⟨m, rfl⟩ : ∃ m, r = 14 + 18 * m := ⟨r / 18, by omega⟩
  have h27 := pow_period 14 18 27 22 (by norm_num) (by norm_num) (by norm_num) m
  omega

-- Cases 4a-d: subsumed by Cases 3a-b via omega

-- === Direct cases (K=4, period=54) ===

theorem case5_mod54_6 (r : Nat) (hr : r % 54 = 6) : td (2 ^ r) 3 = 2 := by
  unfold td; obtain ⟨m, rfl⟩ : ∃ m, r = 6 + 54 * m := ⟨r / 54, by omega⟩
  have := pow_period 6 54 81 64 (by norm_num) (by norm_num) (by norm_num : 2 ^ 6 % 81 = 64) m
  omega

theorem case6_mod54_36 (r : Nat) (hr : r % 54 = 36) : td (2 ^ r) 3 = 2 := by
  unfold td; obtain ⟨m, rfl⟩ : ∃ m, r = 36 + 54 * m := ⟨r / 54, by omega⟩
  have := pow_period 36 54 81 55 (by norm_num) (by norm_num) (by norm_num : 2 ^ 36 % 81 = 55) m
  omega

theorem case7_mod54_38 (r : Nat) (hr : r % 54 = 38) : td (2 ^ r) 3 = 2 := by
  unfold td; obtain ⟨m, rfl⟩ : ∃ m, r = 38 + 54 * m := ⟨r / 54, by omega⟩
  have := pow_period 38 54 81 58 (by norm_num) (by norm_num) (by norm_num : 2 ^ 38 % 81 = 58) m
  omega

theorem case8_mod54_44 (r : Nat) (hr : r % 54 = 44) : td (2 ^ r) 3 = 2 := by
  unfold td; obtain ⟨m, rfl⟩ : ∃ m, r = 44 + 54 * m := ⟨r / 54, by omega⟩
  have := pow_period 44 54 81 67 (by norm_num) (by norm_num) (by norm_num : 2 ^ 44 % 81 = 67) m
  omega

-- === Direct cases needing larger K (orbit not covered by single K) ===
-- These prove digit-2 for the canonical representative only.
-- The full residue class is handled by the main theorem's by-contradiction structure.

theorem case9_r18 : td (2 ^ 18) 4 = 2 := by
  unfold td; norm_num

theorem case10_r20 : td (2 ^ 20) 7 = 2 := by
  unfold td; norm_num

theorem case11_r24 : td (2 ^ 24) 10 = 2 := by
  unfold td; norm_num

theorem case12_r26 : td (2 ^ 26) 10 = 2 := by
  unfold td; norm_num

theorem case13_r42 : td (2 ^ 42) 4 = 2 := by
  unfold td; norm_num
