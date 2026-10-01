import Mathlib.Tactic

-- Step 1: w % 3^(i+1) / 3^i < 3
private lemma mod_pow_lt (w i : ℕ) : w % 3^(i+1) / 3^i < 3 := by
  have h1 := Nat.mod_lt (3^(i+1)) (by positivity)
  have h2 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  rw [h2] at h1
  have := (Nat.div_lt_iff_lt_mul (show 0 < 3^i from by positivity)).mp
  -- Actually let me just use omega approach
  have : w % 3^(i+1) < 3^i * 3 := by rwa [h2]
  omega

-- Step 2: div_mod_eq: w / 3^i % 3 = w % 3^(i+1) / 3^i
private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  have h := Nat.div_add_mod w (3^(i+1))
  rw [h31] at h
  -- h : w / (3^i * 3) * (3^i * 3) + w % (3^i * 3) = w
  -- From h: w = w / (3^i * 3) * (3^i * 3) + w % (3^i * 3)
  -- So: w / 3^i = (w / (3^i * 3) * (3^i * 3) + w % (3^i * 3)) / 3^i
  --            = w / (3^i * 3) * 3 + w % (3^i * 3) / 3^i
  rw [show w = w / (3^i * 3) * (3^i * 3) + w % (3^i * 3) from h ▸ by ring_nf at h; exact h]
  sorry

-- Let me try a completely different approach: prove it with decide for concrete values
-- and by omega for general
-- Actually the issue is omega can't handle div/mod.
-- Let me try simp + omega approach

-- The key identity: w / 3^i % 3 only depends on w % 3^(i+1)
-- Specifically: w / 3^i % 3 = (w % 3^(i+1)) / 3^i
-- This is because w = q * 3^(i+1) + r where r = w % 3^(i+1) < 3^(i+1)
-- So w / 3^i = q * 3 + r / 3^i  [since 3^(i+1) = 3 * 3^i]
-- And (w / 3^i) % 3 = (q * 3 + r / 3^i) % 3 = r / 3^i [since 3 | q*3 and r/3^i < 3]

-- Let me try using omega at the end after establishing key equalities
-- approach: unfold w, do the division, use omega for mod

-- Actually, let me try a radically different approach: prove everything with omega
-- by expressing the digit extraction as a function of modular arithmetic

-- For the overall proof of no_births_after_K7, I'll avoid the digit lemma entirely.
-- Instead, I'll prove it for K = 8..11 directly (mass1_in_NK is small enough to compute),
-- and for K ≥ 12 I'll use mass1_in_NK_empty.

-- The key observation: if mass1_in_NK K = [], then no_births_after_K7 for K is trivially true
-- (vacuously true: there is no r ∈ computeNK K with isMassOneForm r).

-- For K ≥ 12: mass1_in_NK K = [] is already proved!
-- So no_births_after_K7 for K ≥ 12 follows immediately from mass1_in_NK_empty.

-- Wait, no: no_births_after_K7 says "for all K > 7, for all r ∈ computeNK K,
-- if isMassOneForm r, then exists parent in computeNK (K-1)".
-- If mass1_in_NK K = [], that means no r ∈ computeNK K satisfies isMassOneForm r.
-- So the implication is vacuously true!
-- But the statement uses `isMassOneForm r` not `r ∈ mass1_in_NK K`.
-- However, if no r ∈ computeNK K has isMassOneForm r, then the hypothesis is never
-- satisfied, so the theorem is vacuously true.

-- For K = 8,9,10,11: we need a direct proof.
-- But actually, we can compute mass1_in_NK for these values too!

-- Let me check: what are the mass1_in_NK values for K=8,9,10,11?
