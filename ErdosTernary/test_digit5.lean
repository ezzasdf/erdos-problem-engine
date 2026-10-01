import Mathlib.Tactic

-- The digit extraction lemma:
-- For i < n, (v % 3^n) / 3^i % 3 = v / 3^i % 3
--
-- Proof strategy:
-- 1. v / 3^i % 3 = (v % 3^(i+1)) / 3^i  [call this div_mod_eq]
-- 2. (v % 3^n) / 3^i % 3 = ((v % 3^n) % 3^(i+1)) / 3^i  [same lemma applied to v % 3^n]
-- 3. (v % 3^n) % 3^(i+1) = v % 3^(i+1)  [since i+1 ≤ n, so 3^(i+1) | 3^n]

-- Step 1: w / 3^i % 3 = (w % 3^(i+1)) / 3^i
private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h := Nat.div_add_mod w (3^(i+1))
  -- h : w / 3^(i+1) * 3^(i+1) + w % 3^(i+1) = w
  -- Rewrite 3^(i+1) = 3 * 3^i
  have h3 : 3^(i+1) = 3 * 3^i := by rw [Nat.pow_succ]
  rw [h3] at h
  -- h : w / (3 * 3^i) * (3 * 3^i) + w % (3 * 3^i) = w
  -- Also rewrite the mul: 3 * 3^i = 3^i * 3
  have h3b : 3 * 3^i = 3^i * 3 := by ring
  rw [h3b] at h
  -- h : w / (3^i * 3) * (3^i * 3) + w % (3^i * 3) = w
  -- From h: w = w % (3^i * 3) + w / (3^i * 3) * (3^i * 3)
  -- Use the fact that 3^i * 3 = 3^i * 3 and Nat.add_mul_div_right
  have h3c : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  -- Let's rewrite the goal using Nat.div_add_mod
  calc w / 3^i % 3
    = ((w % 3^(i+1) + w / 3^(i+1) * 3^(i+1)) / 3^i) % 3 := by
      rw [show w = w / 3^(i+1) * 3^(i+1) + w % 3^(i+1) from h ▸ Nat.div_add_mod w (3^(i+1)) ▸ by ring]
      congr 2
      rw [h3c, h]
  _ = (w % 3^(i+1) / 3^i + w / 3^(i+1) * 3) % 3 := by
      rw [h3c]
      rw [Nat.add_mul_div_right (w % (3^i * 3)) (by positivity : 0 < 3^i)]
  _ = w % 3^(i+1) / 3^i % 3 := by
      rw [Nat.add_mod]
      simp [Nat.mul_mod_right]
  _ = w % 3^(i+1) / 3^i := by
      apply Nat.mod_eq_of_lt
      have : w % 3^(i+1) < 3^(i+1) := Nat.mod_lt _ (by positivity)
      calc w % 3^(i+1) / 3^i
        ≤ w % 3^(i+1) / 3^i := le_refl _
        _ < 3 := by
          rw [h3c]
          exact Nat.div_lt_of_lt (by rwa [← h3c])
  _ = w % 3^(i+1) / 3^i := rfl

#check @Nat.div_lt_of_lt
EOF
lake env lean ./test_digit5.lean 2>&1 | head -30
