import Mathlib.Tactic

-- The digit equality: for i < n, ((v % 3^n) / 3^i) % 3 = (v / 3^i) % 3
-- Proof: v = q * 3^n + r, so for i < n:
--   v / 3^i = q * 3^(n-i) + r / 3^i
--   (v / 3^i) % 3 = (r / 3^i) % 3  since 3 | q * 3^(n-i)

-- Key helper: for a > 0 and i < n, a * 3^(n-i) is divisible by 3
-- because n-i ≥ 1, so 3 | 3^(n-i)
lemma three_dvd_mul_pow3 (a n i : ℕ) (hi : i < n) : 3 ∣ a * 3^(n - i) := by
  have h1 : 1 ≤ n - i := by omega
  have h2 : 3 ∣ 3^(n - i) := by
    use 3^(n - i - 1)
    rw [show n - i = (n - i - 1) + 1 from by omega]
    rw [Nat.pow_succ]
  exact ⟨a * 3^(n - i - 1), by rw [Nat.pow_succ] at h2; linarith [h2]⟩

-- Actually, simpler: 3^(n-i) = 3 * 3^(n-i-1) when n-i ≥ 1
lemma three_mul_pow (n i : ℕ) (hi : i < n) : 3 ∣ 3^(n - i) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ n - i)
  rw [hk, Nat.pow_add, Nat.pow_one]
  exact ⟨3^k, by ring⟩

-- Now the main digit lemma
-- We need: v / 3^i = (v / 3^n) * 3^(n-i) + (v % 3^n) / 3^i

-- Let's try a direct approach using Nat.div_add_mod
-- v = (v / 3^n) * 3^n + v % 3^n
-- We want to compute v / 3^i

-- First: 3^i * (v / 3^i) + v % 3^i = v
-- Also: v = (v / 3^n) * 3^n + v % 3^n
-- So: 3^i * (v / 3^i) + v % 3^i = (v / 3^n) * 3^n + v % 3^n

-- We need: v / 3^i = (v / 3^n) * 3^(n-i) + (v % 3^n) / 3^i

-- Approach: prove it by showing both sides give the same value when multiplied by 3^i and reduced mod 3^i

-- Actually, let me just try omega directly
-- The key insight: the function f(v) = (v / 3^i) % 3 only depends on v % 3^(i+1)
-- So if v1 % 3^(i+1) = v2 % 3^(i+1), then (v1 / 3^i) % 3 = (v2 / 3^i) % 3

-- For our case: v and v % 3^n agree on v % 3^(i+1) when i < n
-- because 3^(i+1) | 3^n when i+1 ≤ n

-- So: v % 3^(i+1) = (v % 3^n) % 3^(i+1)
-- And: (v / 3^i) % 3 = ((v % 3^n) / 3^i) % 3

-- Let me use Nat.div_add_mod directly
-- v = (v / 3^(i+1)) * 3^(i+1) + v % 3^(i+1)
-- v / 3^i = (v / 3^(i+1)) * 3 + (v % 3^(i+1)) / 3^i
-- (v / 3^i) % 3 = (v % 3^(i+1)) / 3^i  (since 0 ≤ (v % 3^(i+1)) / 3^i < 3)

-- Similarly: ((v % 3^n) / 3^i) % 3 = ((v % 3^n) % 3^(i+1)) / 3^i
-- And (v % 3^n) % 3^(i+1) = v % 3^(i+1) when i+1 ≤ n

-- So (v / 3^i) % 3 = (v % 3^(i+1)) / 3^i = ((v % 3^n) % 3^(i+1)) / 3^i = ((v % 3^n) / 3^i) % 3

-- This is the cleanest proof. Let me implement it.

-- Step 1: (v / 3^i) % 3 = (v % 3^(i+1)) / 3^i
lemma div_mod_eq (v i : ℕ) : v / 3^i % 3 = v % 3^(i+1) / 3^i := by
  have h := Nat.div_add_mod v (3^(i+1))
  -- h : v / 3^(i+1) * 3^(i+1) + v % 3^(i+1) = v
  have h3i : 3^i * 3 = 3^(i+1) := by rw [show 3^(i+1) = 3^i * 3^1 from by rw [Nat.pow_one]; ring_nf]; ring
  -- Actually 3^(i+1) = 3 * 3^i
  have h3i2 : 3^(i+1) = 3 * 3^i := by rw [Nat.pow_succ]
  rw [h3i2] at h
  -- h : v / (3 * 3^i) * (3 * 3^i) + v % (3 * 3^i) = v
  have hdiv : v / 3^i = v / (3 * 3^i) * 3 + v % (3 * 3^i) / 3^i := by
    rw [show v = v / (3 * 3^i) * (3 * 3^i) + v % (3 * 3^i) from h.symm]
    rw [show 3 * 3^i = 3^i * 3 from by ring]
    rw [← show v / 3^i = v / 3^i from rfl]
    sorry -- this approach is getting messy
  sorry

-- Let me try a much simpler approach: just omega it
-- Actually omega can't handle div/mod. Let me use decide for the specific case.

-- Key claim: for any v, if hasTrailingDigit2 v K = false then hasTrailingDigit2 (v % 3^(K-1)) (K-1) = false
-- Proof: hasTrailingDigit2 v K = false means no digit 2 in positions 0..K-1
-- hasTrailingDigit2 (v % 3^(K-1)) (K-1) checks positions 0..K-2
-- The digit at position i of (v % 3^(K-1)) equals the digit at position i of v for i < K-1
-- This is because 3^(K-1) | 3^K and digit extraction only looks at lower bits

-- Actually, the simplest proof uses the fact that for i < n:
-- (v % 3^n) / 3^i % 3 = v / 3^i % 3
-- This follows from: v / 3^i % 3 only depends on v % 3^(i+1)
-- and (v % 3^n) % 3^(i+1) = v % 3^(i+1) when i+1 ≤ n

-- Key helper: the lower k ternary digits of v are determined by v % 3^k
-- Specifically: for i < k, digit i of v = digit i of (v % 3^k)
-- where digit i of w = (w / 3^i) % 3

-- Let me prove this using the characterization:
-- w / 3^i % 3 = w % 3^(i+1) / 3^i
-- This is because w = (w / 3^(i+1)) * 3^(i+1) + w % 3^(i+1)
-- So w / 3^i = (w / 3^(i+1)) * 3 + w % 3^(i+1) / 3^i
-- So w / 3^i % 3 = w % 3^(i+1) / 3^i % 3 = w % 3^(i+1) / 3^i
-- (the last step because 0 ≤ w % 3^(i+1) / 3^i < 3)

-- And: (v % 3^n) % 3^(i+1) = v % 3^(i+1) when i+1 ≤ n
-- This is Nat.mod_mod_of_dvd: v % 3^(i+1) % 3^n = v % 3^(i+1) when ... no
-- Actually: v % 3^n % 3^(i+1) = v % 3^(i+1) when 3^(i+1) | 3^n

-- Hmm wait, v % 3^n is smaller than 3^n, so (v % 3^n) % 3^(i+1) = v % 3^n when 3^(i+1) > 3^n
-- That's the wrong direction.

-- For i+1 ≤ n: 3^(i+1) ≤ 3^n, so v % 3^n could be larger than 3^(i+1)
-- But (v % 3^n) % 3^(i+1) = v % 3^(i+1) because:
-- v = q * 3^n + r where r = v % 3^n < 3^n
-- v % 3^(i+1) = (q * 3^n + r) % 3^(i+1)
-- Since 3^(i+1) | 3^n (because i+1 ≤ n):
-- v % 3^(i+1) = r % 3^(i+1) = (v % 3^n) % 3^(i+1)

-- This is Nat.mod_mod_of_dvd: a % (b * c) % c = a % c
-- Or more precisely: a % n % m = a % m when m | n
-- In Lean 4: Nat.mod_mod_of_dvd : c ∣ b → a % b % c = a % c

-- OK so the proof chain is:
-- 1. For i < K-1: digit i of (v % 3^(K-1)) = ((v % 3^(K-1)) % 3^(i+1)) / 3^i
--    by the div_mod_eq lemma (which we need to prove)
-- 2. ((v % 3^(K-1)) % 3^(i+1)) = v % 3^(i+1) since i+1 ≤ K-1 so 3^(i+1) | 3^(K-1)
--    by Nat.mod_mod_of_dvd
-- 3. digit i of v = (v % 3^(i+1)) / 3^i by the same div_mod_eq lemma
-- So digit i of (v % 3^(K-1)) = digit i of v

-- This is the full proof! But I still need to prove div_mod_eq.

-- Let me try: w / 3^i % 3 = w % 3^(i+1) / 3^i

-- w = (w / 3^(i+1)) * 3^(i+1) + w % 3^(i+1)
-- w / 3^i = ?

-- Actually, the identity w / 3^i % 3 = w % 3^(i+1) / 3^i is well-known.
-- Let me try to prove it in Lean.

-- In Lean 4, there might be a lemma like Nat.div_mod_div or similar.
-- Let me check:
#check @Nat.div_div_eq_div_mul -- m / n / k = m / (n * k)
#check @Nat.div_mod -- w / n * n + w % n = w
#check @Nat.add_mul_div_right -- (a + c * b) / c = a / c + b when c > 0

-- Key: w / 3^i where w = (w / 3^(i+1)) * 3^(i+1) + w % 3^(i+1)
-- 3^i * 3 = 3^(i+1), so:
-- w / 3^i = ((w / 3^(i+1)) * 3 * 3^i + w % 3^(i+1)) / 3^i
-- By Nat.add_mul_div_right:
-- = (w / 3^(i+1)) * 3 + (w % 3^(i+1)) / 3^i
-- Wait, but Nat.add_mul_div_right says (a + c * b) / c = a / c + b
-- So ((w / 3^(i+1)) * 3^(i+1) + w % 3^(i+1)) / 3^i
-- Hmm, 3^(i+1) is not of the form 3^i * b directly.

-- Actually: 3^(i+1) = 3 * 3^i
-- So: w = (w / 3^(i+1)) * 3 * 3^i + w % 3^(i+1)
-- By Nat.add_mul_div_right (with c = 3^i, a = w % 3^(i+1), b = (w / 3^(i+1)) * 3):
-- (w % 3^(i+1) + 3^i * ((w / 3^(i+1)) * 3)) / 3^i
--   = w % 3^(i+1) / 3^i + (w / 3^(i+1)) * 3

-- Hmm wait, Nat.add_mul_div_right says: (a + c * b) / c = a / c + b when c > 0
-- So: (w % 3^(i+1) + 3^i * ((w / 3^(i+1)) * 3)) / 3^i
--   = w % 3^(i+1) / 3^i + (w / 3^(i+1)) * 3

-- But we have: w = (w / 3^(i+1)) * 3 * 3^i + w % 3^(i+1)
-- = w % 3^(i+1) + (w / 3^(i+1)) * 3 * 3^i
-- = w % 3^(i+1) + 3^i * ((w / 3^(i+1)) * 3)

-- So: w / 3^i = (w % 3^(i+1) + 3^i * ((w / 3^(i+1)) * 3)) / 3^i
--   = w % 3^(i+1) / 3^i + (w / 3^(i+1)) * 3

-- Therefore: w / 3^i % 3 = (w % 3^(i+1) / 3^i + (w / 3^(i+1)) * 3) % 3
--   = w % 3^(i+1) / 3^i % 3 + 0 % 3
--   = w % 3^(i+1) / 3^i % 3

-- And since 0 ≤ w % 3^(i+1) / 3^i < 3:
--   = w % 3^(i+1) / 3^i

-- Great! So the proof is:
-- 1. w = w % 3^(i+1) + 3^i * (w / 3^(i+1) * 3)  [by Nat.div_add_mod and algebra]
-- 2. w / 3^i = w % 3^(i+1) / 3^i + w / 3^(i+1) * 3  [by Nat.add_mul_div_right]
-- 3. w / 3^i % 3 = w % 3^(i+1) / 3^i  [by mod arithmetic]

-- Let me implement this.

-- Actually, let me check if Nat.add_mul_div_right exists
#check @Nat.add_mul_div_right
-- Nat.add_mul_div_right : (a : ℕ) → {b : ℕ} → 0 < b → (a + c * b) / b = a / b + c

-- Perfect! So with a = w % 3^(i+1), b = 3^i, c = (w / 3^(i+1)) * 3:
-- (w % 3^(i+1) + (w / 3^(i+1)) * 3 * 3^i) / 3^i
--   = w % 3^(i+1) / 3^i + (w / 3^(i+1)) * 3

-- Now, w = w % 3^(i+1) + (w / 3^(i+1)) * 3^(i+1)
--   = w % 3^(i+1) + (w / 3^(i+1)) * 3 * 3^i  [since 3^(i+1) = 3 * 3^i]

-- So w / 3^i = w % 3^(i+1) / 3^i + (w / 3^(i+1)) * 3

-- Then: w / 3^i % 3 = (w % 3^(i+1) / 3^i + (w / 3^(i+1)) * 3) % 3
--   = (w % 3^(i+1) / 3^i + (w / 3^(i+1)) * 3) % 3

-- By Nat.add_mod:
--   = ((w % 3^(i+1) / 3^i) % 3 + ((w / 3^(i+1)) * 3) % 3) % 3

-- And ((w / 3^(i+1)) * 3) % 3 = 0 because 3 | (w / 3^(i+1)) * 3

-- So w / 3^i % 3 = (w % 3^(i+1) / 3^i) % 3

-- And since 0 ≤ w % 3^(i+1) / 3^i < 3:
-- (w % 3^(i+1) / 3^i) % 3 = w % 3^(i+1) / 3^i

-- Hmm actually, do I need this last step? If I'm going to compare two expressions of the form X % 3, I just need them to be equal after the mod. So:
-- w / 3^i % 3 = (w % 3^(i+1) / 3^i) % 3

-- This is enough for the proof.

-- Let me implement this in Lean 4.
