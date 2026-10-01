import Mathlib.Tactic

private lemma pow3_pos (i : ℕ) : 0 < 3^i :=
  Nat.pow_pos (show 0 < 3 from by norm_num)

private lemma mod3_pow3_lt (w i : ℕ) : w % 3^(i+1) / 3^i < 3 := by
  have h := Nat.mod_lt (3^(i+1)) (pow3_pos (i+1))
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  rw [h31] at h
  exact (Nat.div_lt_iff_lt_mul (pow3_pos i)).mpr h

private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  have hp : 0 < 3^i := pow3_pos i
  -- Key identity: w / 3^i = w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i
  have h_key : w / 3^i = w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i := by
    have h := Nat.div_add_mod w (3^(i+1))
    -- h : 3^(i+1) * (w / 3^(i+1)) + w % 3^(i+1) = w
    -- Show w / 3^i = ... using transitivity
    calc w / 3^i
        = (3^(i+1) * (w / 3^(i+1)) + w % 3^(i+1)) / 3^i := by
            rw [show w = 3^(i+1) * (w / 3^(i+1)) + w % 3^(i+1) from h ▸ by linarith]
      _ = (w % 3^(i+1) + 3^(i+1) * (w / 3^(i+1))) / 3^i := by ring_nf
      _ = (w % 3^(i+1) + (w / 3^(i+1) * 3) * 3^i) / 3^i := by
            congr 1
            rw [h31]
            ring_nf
      _ = w % 3^(i+1) / 3^i + w / 3^(i+1) * 3 :=
            Nat.add_mul_div_right _ _ hp
  -- Now use h_key
  rw [h_key, Nat.add_mod]
  have : (w / 3^(i+1) * 3) % 3 = 0 := Nat.mul_mod_left _ _
  rw [this, Nat.zero_add]
  exact Nat.mod_eq_of_lt (mod3_pow3_lt w i)

-- Test
#eval (div_mod_eq 42 1 : True)
#eval (div_mod_eq 100 2 : True)
