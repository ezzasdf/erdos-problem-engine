import Mathlib.Tactic

private lemma pow3_pos (i : ℕ) : 0 < 3^i :=
  Nat.pow_pos (show 0 < 3 from by norm_num)

private lemma mod3_pow3_lt (w i : ℕ) : w % 3^(i+1) / 3^i < 3 := by
  have h := Nat.mod_lt (3^(i+1)) (pow3_pos (i+1))
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  rw [h31] at h
  exact (Nat.div_lt_iff_lt_mul (pow3_pos i)).mpr h

private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h := Nat.div_add_mod w (3^(i+1))
  have hw : w = w % 3^(i+1) + w / 3^(i+1) * 3 * 3^i := by
    linarith [show 3^(i+1) * (w / 3^(i+1)) = w / 3^(i+1) * 3 * 3^i from by ring]
  rw [hw, show w / 3^(i+1) * 3 * 3^i = (w / 3^(i+1) * 3) * 3^i from by ring]
  rw [Nat.add_mul_div_right _ _ (pow3_pos i)]
  rw [Nat.add_mod]
  rw [Nat.mul_mod_left]
  rw [Nat.zero_add]
  exact Nat.mod_eq_of_lt (mod3_pow3_lt w i)

private lemma digit_of_mod (v n i : ℕ) (hi : i < n) :
    (v % 3^n) / 3^i % 3 = v / 3^i % 3 := by
  rw [div_mod_eq, ← div_mod_eq]
  rw [Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow _ (by omega : i + 1 ≤ n)

#eval div_mod_eq 42 1
#eval (42 % 3^2 / 3^1 % 3 = 42 / 3^1 % 3 : Bool)
