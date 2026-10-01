import Mathlib.Tactic

-- Can omega prove the general case?
example (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  sorry

-- Key question: does omega handle 3^i?
-- Let me check step by step
-- For i = 0: w / 1 % 3 = w % 3 / 1  → w % 3 = w % 3 ✓
-- For i = 1: w / 3 % 3 = w % 9 / 3 ✓ (omega proves it)
-- For i = 2: w / 9 % 3 = w % 27 / 9

-- Test: omega with pow
example (w i : ℕ) : w / 3^i * 3^i + w % 3^i = w := by omega
example (w i : ℕ) : w % 3^i < 3^i := by omega
example (w i : ℕ) : w / 3^i ≤ w := by omega

-- Actually, omega might not handle 3^i as it's not linear in i
-- Let me check with a concrete exponentiation
-- In omega, 3^i is treated as a variable, and the constraint 3^i > 0 is needed

-- Let me test the digit lemma for i = 0, 1, 2, 3 and see if omega can do it
-- when we also have the div_add_mod hypothesis
example (w : ℕ) : w / 3^0 % 3 = w % 3^1 / 3^0 := by norm_num
example (w : ℕ) : w / 3^1 % 3 = w % 3^2 / 3^1 := by omega
example (w : ℕ) : w / 3^2 % 3 = w % 3^3 / 3^2 := by omega
example (w : ℕ) : w / 3^3 % 3 = w % 3^4 / 3^3 := by omega

-- Can omega do it for general i?
-- If not, maybe we can prove it by induction on i
-- Base case: i = 0, trivially w % 3 = w % 3
-- Inductive step: w / 3^(i+1) % 3 = w % 3^(i+2) / 3^(i+1)
--   This follows from (w/3) / 3^i % 3 = (w/3) % 3^(i+1) / 3^i (IH applied to w/3)
--   and w / 3^(i+1) = (w/3) / 3^i... no that's not right.

-- Actually, the inductive step would be:
-- w / 3^(i+1) % 3 = w / (3 * 3^i) % 3
--                   = w / 3 / 3^i % 3  (by div_div_eq_div_mul)
--                   = (w / 3) % 3^(i+1) / 3^i  (by IH applied to w/3)
--                   = ((w / 3) % 3^(i+1)) / 3^i
-- Now I need: ((w / 3) % 3^(i+1)) / 3^i = w % 3^(i+2) / 3^(i+1)
-- Hmm, this is essentially the same digit lemma applied to w/3.
-- So induction doesn't simplify things.

-- The key: omega handles the specific cases because it can expand 3^0=1, 3^1=3, 3^2=9, etc.
-- For general i, omega can't expand 3^i.

-- But! We can prove it using the fact that both sides equal
-- the i-th ternary digit, which can be characterized as:
-- d = w / 3^i % 3 iff w = q * 3^(i+1) + d * 3^i + r where 0 ≤ d < 3 and 0 ≤ r < 3^i

-- Actually, let me try another approach: prove it using Nat.div_add_mod twice
-- and omega for the final step

example (w i : ℕ) (hi : 1 ≤ i) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  sorry
