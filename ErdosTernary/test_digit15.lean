import Mathlib.Tactic

private lemma pow3_pos (i : ℕ) : 0 < 3^i :=
  Nat.pow_pos (show 0 < 3 from by norm_num)

private lemma mod3_pow3_lt (w i : ℕ) : w % 3^(i+1) / 3^i < 3 := by
  have h := Nat.mod_lt (3^(i+1)) (pow3_pos (i+1))
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  rw [h31] at h
  exact (Nat.div_lt_iff_lt_mul (pow3_pos i)).mpr h

-- Key: w / 3^i % 3 = w % 3^(i+1) / 3^i
-- Use conv to rewrite only the LHS
private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  have hp : 0 < 3^i := pow3_pos i
  -- Establish: w / 3^i = w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i
  -- via: w = w % 3^(i+1) + w / 3^(i+1) * 3 * 3^i
  have hw : w = w % 3^(i+1) + w / 3^(i+1) * 3 * 3^i := by
    have h := Nat.div_add_mod w (3^(i+1))
    rw [h31, mul_comm (3^i)] at h
    linarith
  have hdiv : w / 3^i = w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i := by
    rw [hw, show w / 3^(i+1) * 3 * 3^i = (w / 3^(i+1) * 3) * 3^i from by ring]
    exact Nat.add_mul_div_right _ _ hp
  rw [hdiv, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add]
  exact Nat.mod_eq_of_lt (mod3_pow3_lt w i)

-- But the issue is: rw [hw] replaces w everywhere, changing the RHS too.
-- Let me verify this compiles:
-- #eval if div_mod_eq 42 1 then "ok" else "fail"
