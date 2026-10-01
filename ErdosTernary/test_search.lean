import Mathlib.Tactic

-- Key: the equation w / 3^i = w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i
-- can be proved with careful rewrites
-- But the rw replaces w everywhere. Let me try using `show` to state a different equation.

-- Actually, the key issue is: how to prove the equation WITHOUT rw replacing w everywhere.

-- NEW IDEA: use `calc` to build up the equality step by step,
-- where each step is a local equality that doesn't involve rewriting w.

example (w i : ℕ) : w / 3^i = w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i := by
  have hp : 0 < 3^i := Nat.pow_pos (show 0 < 3 from by norm_num)
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  -- The proof: w / 3^i = (w / 3^(i+1) * 3^(i+1) + w % 3^(i+1)) / 3^i
  --                      = ((w / 3^(i+1) * 3) * 3^i + w % 3^(i+1)) / 3^i
  --                      = w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i
  -- Step 1: rewrite goal LHS using Nat.div_add_mod
  -- w / 3^i = (3^(i+1) * (w / 3^(i+1)) + w % 3^(i+1)) / 3^i  (since w = ...)
  -- Use show to change the LHS without rw
  show (3^(i+1) * (w / 3^(i+1)) + w % 3^(i+1)) / 3^i = w / 3^(i+1) * 3 + w % 3^(i+1) / 3^i
  sorry
