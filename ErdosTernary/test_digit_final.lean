import Mathlib.Tactic

private lemma pow3_pos (i : ℕ) : 0 < 3^i :=
  Nat.pow_pos (show 0 < 3 from by norm_num)

private lemma three_pow_succ (i : ℕ) : 3^(i+1) = 3 * 3^i := by
  show 3 ^ (Nat.succ i) = 3 * 3 ^ i
  rw [Nat.pow_succ]
  ring

private lemma mod3_pow3_lt (w i : ℕ) : w % 3^(i+1) / 3^i < 3 := by
  have h1 : w % 3^(i+1) < 3^(i+1) := Nat.mod_lt w (pow3_pos (i+1))
  have h2 : w % 3^(i+1) < 3 * 3^i := by rw [← three_pow_succ]; exact h1
  exact (Nat.div_lt_iff_lt_mul (pow3_pos i)).mpr h2

private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have hp : 0 < 3^i := pow3_pos i
  have h31 : 3^(i+1) = 3^i * 3 := (Nat.pow_succ 3 i).symm
  have h := Nat.div_add_mod w (3^(i+1))
  have h_key : w / 3^i = w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i := by
    trans (3^(i+1) * (w / 3^(i+1)) + w % 3^(i+1)) / 3^i
    · congr 1; exact h.symm
    · rw [h31]
      rw [show 3^i * 3 * (w / (3^i * 3)) = (w / (3^i * 3) * 3) * 3^i from by ring]
      rw [show (w / (3^i * 3) * 3) * 3^i + w % (3^i * 3) = w % (3^i * 3) + (w / (3^i * 3) * 3) * 3^i from by ring]
      rw [Nat.add_mul_div_right _ _ hp]
      rw [add_comm]
  have h0 : (w / 3^(i+1)) * 3 % 3 = 0 := Nat.mul_mod_left _ _
  rw [h_key, Nat.add_mod, h0, Nat.zero_add]
  rw [Nat.mod_eq_of_lt (mod3_pow3_lt w i)]
  exact Nat.mod_eq_of_lt (mod3_pow3_lt w i)

private lemma digit_of_mod (v n i : ℕ) (hi : i < n) :
    (v % 3^n) / 3^i % 3 = v / 3^i % 3 := by
  have h1 := div_mod_eq v i
  have h2 := div_mod_eq (v % 3^n) i
  rw [h2, h1]
  congr 1
  rw [Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow _ (by omega : i + 1 ≤ n)
