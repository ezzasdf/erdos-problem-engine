import Mathlib.Tactic

-- Helper: 0 < 3^i
private lemma pow3_pos (i : ℕ) : 0 < 3^i :=
  Nat.pow_pos (norm_num : (0 : ℕ) < 3)

-- The digit extraction lemma
-- w / 3^i % 3 = (w % 3^(i+1)) / 3^i
-- Key idea: w = q * 3^(i+1) + r, so w / 3^i = q * 3 + r / 3^i
-- Then w / 3^i % 3 = (q * 3 + r / 3^i) % 3 = r / 3^i

private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  -- From div_add_mod: w = 3^(i+1) * (w / 3^(i+1)) + w % 3^(i+1)
  have h := Nat.div_add_mod w (3^(i+1))
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  -- Rewrite w = r + q * 3 * 3^i where r = w % 3^(i+1), q = w / 3^(i+1)
  have hw : w = w % 3^(i+1) + w / 3^(i+1) * 3 * 3^i := by
    rw [h31, mul_comm (3^i)] at h
    linarith
  -- Rewrite in goal
  rw [hw]
  -- Goal: (w % 3^(i+1) + w / 3^(i+1) * 3 * 3^i) / 3^i % 3 = w % 3^(i+1) / 3^i
  -- Rewrite 3 * 3^i as 3^i * 3 to match add_mul_div_right pattern
  rw [show w / 3^(i+1) * 3 * 3^i = (w / 3^(i+1) * 3) * 3^i from by ring]
  -- Goal: (w % 3^(i+1) + (w / 3^(i+1) * 3) * 3^i) / 3^i % 3 = ...
  rw [Nat.add_mul_div_right (w % 3^(i+1)) (w / 3^(i+1) * 3) (pow3_pos i)]
  -- Goal: (w % 3^(i+1) / 3^i + w / 3^(i+1) * 3) % 3 = w % 3^(i+1) / 3^i
  rw [Nat.add_mod]
  -- Goal: (w % 3^(i+1) / 3^i % 3 + w / 3^(i+1) * 3 % 3) % 3 = w % 3^(i+1) / 3^i
  have hmod0 : w / 3^(i+1) * 3 % 3 = 0 := Nat.mul_mod_left _ _
  rw [hmod0, Nat.zero_add]
  -- Goal: w % 3^(i+1) / 3^i % 3 = w % 3^(i+1) / 3^i
  -- Since w % 3^(i+1) < 3^(i+1) = 3^i * 3, dividing by 3^i gives < 3
  have hlt : w % 3^(i+1) < 3^i * 3 := by
    have := Nat.mod_lt (3^(i+1)) (pow3_pos (i+1))
    rwa [h31]
  exact Nat.mod_eq_of_lt ((Nat.div_lt_iff_lt_mul (pow3_pos i)).mpr hlt)

-- Now prove digit_of_mod: for i < n, (v % 3^n) / 3^i % 3 = v / 3^i % 3
private lemma digit_of_mod (v n i : ℕ) (hi : i < n) :
    (v % 3^n) / 3^i % 3 = v / 3^i % 3 := by
  rw [div_mod_eq, ← div_mod_eq]
  -- Need: (v % 3^n) % 3^(i+1) = v % 3^(i+1)
  rw [Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow _ (by omega : i + 1 ≤ n)

-- Now prove the trailing digit subset
-- hasTrailingDigit2 v K = false → hasTrailingDigit2 (v % 3^(K-1)) (K-1) = false
-- Note: hasTrailingDigit2 is defined in BridgeCompute
-- hasTrailingDigit2 val K = (List.range K).any fun i => (val / 3 ^ i) % 3 == 2

-- For the final proof, we need to import hasTrailingDigit2
-- But let's just prove the helper and use it in the main file
