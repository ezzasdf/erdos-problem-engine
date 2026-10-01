import Mathlib.Tactic

-- Test if omega can handle this
example (w i : ℕ) (hi : i < 5) : w % 3^(i+1) / 3^i < 3 := by
  sorry

example (w i : ℕ) (hi : i < 5) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  sorry

-- Test with omega
example (a b : ℕ) : a % b < b ∨ b = 0 := by omega

-- Test: can omega handle division patterns?
example (w : ℕ) : w / 3 * 3 + w % 3 = w := by omega
example (w : ℕ) : w % 3 = w - w / 3 * 3 := by omega
example (w : ℕ) : w % 3 ≤ w := by omega
example (w : ℕ) : w % 3 < 3 := by omega
example (w : ℕ) : w / 3 ≤ w := by omega

-- Test the key identity
example (w i : ℕ) : w % 3^(i+1) / 3^i ≤ 2 := by omega
example (w i : ℕ) : w / 3^i % 3 ≤ 2 := by omega
