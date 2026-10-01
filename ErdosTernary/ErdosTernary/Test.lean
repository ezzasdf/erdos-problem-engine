import Mathlib.Tactic

def td (n k : Nat) : Nat := (n / 3 ^ k) % 3

-- Can omega handle (9*q + 7)/3 directly?
example (q : Nat) : (9 * q + 7) / 3 = 3 * q + 2 := by omega

-- Can omega handle the bridge directly?
example (n : Nat) (h : n % 9 = 7) : (n / 3) % 3 = 2 := by omega

-- Can omega handle 2^(4+6*m) % 9 = 7? Probably not (exponentiation).
-- But we can do it with induction + norm_num + omega.
example (m : Nat) : 2 ^ (4 + 6 * m) % 9 = 7 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    simp only [show 4 + 6 * (m + 1) = (4 + 6 * m) + 6 from by omega]
    rw [Nat.pow_add, Nat.mul_mod, ih, show 2 ^ 6 % 9 = 1 from by norm_num]
    norm_num

-- General pattern: 2^(a + T*m) % M = v
-- where 2^T % M = 1
-- Proved by: 2^(a+T*m) = 2^a * (2^T)^m, and (2^T)^m % M = 1^m % M = 1
-- So 2^(a+T*m) % M = (2^a % M) * 1 % M = 2^a % M = v
-- We encode this as: rw [Nat.pow_add, Nat.pow_mul, h_T, Nat.pow_one, ...]

-- Key building block: show (2^T)^m % M = 1 given 2^T % M = 1
theorem pow_mod_eq_one (T M m : Nat) (h : 2 ^ T % M = 1) : (2 ^ T) ^ m % M = 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih, h, Nat.one_mul]

-- 2^(a + T*m) % M = v when 2^T % M = 1 and 2^a % M = v
theorem pow_add_mod (a T M m : Nat) (hT : 2 ^ T % M = 1) (ha : 2 ^ a % M = v) :
    2 ^ (a + T * m) % M = v := by
  rw [Nat.pow_add, Nat.mul_mod, Nat.pow_mul, pow_mod_eq_one T M m hT, Nat.one_mul, ha]

-- Case 1: r odd -> td(2^r, 0) = 2
-- 2^r % 3 = 2 for odd r
theorem pow2_mod3_odd (r : Nat) (hr : r % 2 = 1) : 2 ^ r % 3 = 2 := by
  omega -- does this work?

-- Case 2: r%6=4 -> td(2^r, 1) = 2
-- 2^r % 9 = 7 for r%6=4, so (2^r / 3) % 3 = 2
theorem case2 (r : Nat) (hr : r % 6 = 4) : td (2 ^ r) 1 = 2 := by
  unfold td
  have h9 : 2 ^ r % 9 = 7 := by
    obtain ⟨m, rfl⟩ : ∃ m, r = 4 + 6 * m := by
      exact ⟨r / 6, by omega⟩
    exact pow_add_mod 4 6 9 m (by norm_num) (by norm_num)
  omega
