import Mathlib.Tactic

-- Test: conv_lhs only rewrites the LHS
example (a b c : Nat) (h : a = b) : a + c = b + c := by
  conv_lhs => rw [h]
  rfl

-- Now test with div_mod_eq
-- The issue is: rw replaces w everywhere.
-- conv_lhs should only replace in the LHS.

example (w i : ℕ) (hp : 0 < 3^i) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  have h := Nat.div_add_mod w (3^(i+1))
  -- h : 3^(i+1) * (w / 3^(i+1)) + w % 3^(i+1) = w
  -- Use conv_lhs to rewrite w on the LHS only
  conv_lhs => 
    rw [show w = 3^(i+1) * (w / 3^(i+1)) + w % 3^(i+1) from h ▸ by ring_nf]
    rw [h31]
  -- Goal should now be: (3^i * 3 * (w / (3^i * 3)) + w % (3^i * 3)) / 3^i % 3 = w % 3^(i+1) / 3^i
  -- but wait, conv_lhs rewrites w only on the LHS, so RHS is still w % 3^(i+1) / 3^i
  sorry
