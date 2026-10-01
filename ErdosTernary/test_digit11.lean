import Mathlib.Tactic

-- Check key lemma signatures
#check @Nat.mul_mod_right  -- m * n % m = 0
#check @Nat.mul_mod_left   -- n * m % m = 0

-- Helper: 0 < 3^i
private lemma pow3_pos (i : ℕ) : 0 < 3^i :=
  Nat.pow_pos (norm_num.pos : (0 : ℕ) < 3)

-- Step 1: w % 3^(i+1) / 3^i < 3
private lemma mod3_pow3_lt (w i : ℕ) : w % 3^(i+1) / 3^i < 3 := by
  have h := Nat.mod_lt (3^(i+1)) (pow3_pos (i+1))
  have h2 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  rw [h2] at h
  omega

-- Step 2: w / 3^i % 3 = (w % 3^(i+1)) / 3^i
private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  have h := Nat.div_add_mod w (3^(i+1))
  -- h : w / 3^(i+1) * 3^(i+1) + w % 3^(i+1) = w
  -- Rewrite goal using w = w / 3^(i+1) * 3^(i+1) + w % 3^(i+1)
  rw [show w = w / 3^(i+1) * 3^(i+1) + w % 3^(i+1) from h ▸ rfl]
  -- Now goal: (w / 3^(i+1) * 3^(i+1) + w % 3^(i+1)) / 3^i % 3 = w % 3^(i+1) / 3^i
  rw [h31]
  -- goal: (w / 3^(i+1) * (3^i * 3) + w % 3^(i+1)) / 3^i % 3 = w % 3^(i+1) / 3^i
  -- Rewrite to: (w % 3^(i+1) + (w / 3^(i+1) * 3) * 3^i) / 3^i % 3
  rw [show w / 3^(i+1) * (3^i * 3) + w % 3^(i+1) = w % 3^(i+1) + (w / 3^(i+1) * 3) * 3^i from by ring]
  -- Apply Nat.add_mul_div_right: (a + b * c) / c = a / c + b when c > 0
  rw [Nat.add_mul_div_right (w % 3^(i+1)) (w / 3^(i+1) * 3) (pow3_pos i)]
  -- goal: (w % 3^(i+1) / 3^i + w / 3^(i+1) * 3) % 3 = w % 3^(i+1) / 3^i
  rw [Nat.add_mod]
  -- goal: (w % 3^(i+1) / 3^i % 3 + w / 3^(i+1) * 3 % 3) % 3 = w % 3^(i+1) / 3^i
  have hmod0 : w / 3^(i+1) * 3 % 3 = 0 := by
    rw [Nat.mul_mod_left]
  rw [hmod0, Nat.zero_add]
  -- goal: w % 3^(i+1) / 3^i % 3 = w % 3^(i+1) / 3^i
  exact Nat.mod_eq_of_lt (mod3_pow3_lt w i)

#check @Nat.mul_mod_left
