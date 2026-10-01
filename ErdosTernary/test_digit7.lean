import Mathlib.Tactic

-- Check exact signatures
#check @Nat.div_lt_iff_lt_mul
#check @Nat.add_mul_div_right
#check @Nat.mod_mod_of_dvd
#check @Nat.pow_dvd_pow
#check @Nat.mod_eq_of_lt
#check @Nat.mod_lt

-- Step 1: w % 3^(i+1) / 3^i < 3
private lemma mod_pow_lt (w i : ℕ) : w % 3^(i+1) / 3^i < 3 := by
  have h1 := Nat.mod_lt (3^(i+1)) (by positivity : 0 < 3^(i+1))
  have h2 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  rw [h2] at h1
  exact (Nat.div_lt_iff_lt_mul (by positivity : 0 < 3^i)).mpr h1

-- Step 2: div_mod_eq: w / 3^i % 3 = w % 3^(i+1) / 3^i
private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  have h := Nat.div_add_mod w (3^(i+1))
  rw [h31] at h
  -- h : w / (3^i * 3) * (3^i * 3) + w % (3^i * 3) = w
  -- From h: w = w % (3^i * 3) + w / (3^i * 3) * (3^i * 3)
  -- Rewrite 3^i * 3 = 3^i * 3, use add_mul_div_right
  have hdiv : w / 3^i = w % (3^i * 3) / 3^i + w / (3^i * 3) * 3 := by
    rw [show w = w % (3^i * 3) + w / (3^i * 3) * (3^i * 3) from by linarith [h]]
    rw [Nat.add_mul_div_right _ (by positivity : 0 < 3^i)]
  rw [hdiv]
  rw [Nat.add_mod]
  have hmul3 : (w / (3^i * 3) * 3) % 3 = 0 := by
    rw [Nat.mul_mod]
    simp
  rw [hmul3, Nat.zero_add]
  exact Nat.mod_eq_of_lt (mod_pow_lt w i)
