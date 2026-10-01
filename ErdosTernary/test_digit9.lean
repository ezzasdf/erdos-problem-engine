import Mathlib.Tactic

-- div_mod_eq: w / 3^i % 3 = (w % 3^(i+1)) / 3^i
-- Proof: w = q * 3^(i+1) + r, so w / 3^i = r / 3^i + q * 3
-- and (r / 3^i + q * 3) % 3 = r / 3^i % 3 = r / 3^i

private lemma pow3_pos (i : ℕ) : 0 < 3^i := by positivity

private lemma mod3_pow3_lt (w i : ℕ) : w % 3^(i+1) / 3^i < 3 := by
  have h := Nat.mod_lt (3^(i+1)) (by positivity)
  have h2 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  rw [h2] at h
  exact (Nat.div_lt_iff_lt_mul (pow3_pos i)).mpr h

private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  have h := Nat.div_add_mod w (3^(i+1))
  rw [h31] at h
  -- h : w / (3^i * 3) * (3^i * 3) + w % (3^i * 3) = w
  -- Rewrite: w = w % 3^(i+1) + w / 3^(i+1) * 3 * 3^i
  rw [h31, show w = w % (3^i * 3) + w / (3^i * 3) * 3 * 3^i from by linarith [h]] at *
  -- Actually let me just rewrite in the goal
  rw [show w = w % 3^(i+1) + w / 3^(i+1) * 3 * 3^i from by linarith [h, show w = w / 3^(i+1) * 3^(i+1) + w % 3^(i+1) from Nat.div_add_mod w (3^(i+1)) ▸ by ring_nf])
  sorry

-- Let me try a cleaner approach
private lemma div_mod_eq' (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  -- w = (w / 3^(i+1)) * 3^(i+1) + w % 3^(i+1)
  have h := Nat.div_add_mod w (3^(i+1))
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  -- w / 3^i = (w / 3^(i+1)) * 3 + (w % 3^(i+1)) / 3^i
  have hdiv : w / 3^i = w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i := by
    rw [h31] at h
    have : w = w % (3^i * 3) + w / (3^i * 3) * (3^i * 3) := by linarith [h]
    rw [this]
    rw [show 3^i * 3 = 3 * 3^i from by ring]
    rw [show w % (3^i * 3) + w / (3^i * 3) * (3 * 3^i) = w % (3^i * 3) + (w / (3^i * 3) * 3) * 3^i from by ring]
    rw [Nat.add_mul_div_right _ (pow3_pos i)]
  -- Now w / 3^i % 3 = (w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i) % 3
  rw [hdiv]
  rw [Nat.add_mod]
  -- (w / 3^(i+1) * 3) % 3 = 0
  simp [Nat.mul_mod_right]
  -- Now need: (0 + w % 3^(i+1) / 3^i) % 3 = w % 3^(i+1) / 3^i
  rw [Nat.zero_add]
  exact Nat.mod_eq_of_lt (mod3_pow3_lt w i)

#check @Nat.add_mul_div_right
