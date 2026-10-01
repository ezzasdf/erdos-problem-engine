import Mathlib.Tactic

-- The key fact: for i < n, ((v % 3^n) / 3^i) % 3 = (v / 3^i) % 3
-- Equivalently: v / 3^i % 3 = v % 3^n / 3^i % 3 when i < n

-- Approach: use v = (v / 3^n) * 3^n + v % 3^n
-- Then v / 3^i = (v / 3^n) * 3^(n-i) + (v % 3^n) / 3^i
-- So v / 3^i % 3 = ((v / 3^n) * 3^(n-i)) % 3 + (v % 3^n) / 3^i % 3 % 3
-- Since n-i ≥ 1, ((v / 3^n) * 3^(n-i)) % 3 = 0
-- So v / 3^i % 3 = (v % 3^n) / 3^i % 3

-- Actually let me try using Nat.div_div_eq_div_mul
#check @Nat.div_div_eq_div_mul

-- And the key fact: a * b / a = b when a > 0
#check @Nat.mul_div_cancel_left

-- Let me try a simpler approach: just use omega
-- The digit extraction (v / 3^i) % 3 is the same for v and v % 3^n
-- because v = q * 3^n + r and r < 3^n, so for i < n:
-- v / 3^i = q * 3^(n-i) + r / 3^i
-- (v / 3^i) % 3 = (q * 3^(n-i) + r / 3^i) % 3
-- Since n-i ≥ 1, q * 3^(n-i) is divisible by 3
-- So (v / 3^i) % 3 = (r / 3^i) % 3

-- Let me try this approach in Lean
-- First, prove v / 3^i = (v / 3^n) * 3^(n-i) + (v % 3^n) / 3^i for i < n
-- This requires showing that (v / 3^n) * 3^n and v % 3^n can be split

-- Actually, the cleanest way might be to use the fact that
-- a % b % c = a % c when c | b
-- Let me check:
#check @Nat.mod_mod_of_dvd
-- Nat.mod_mod_of_dvd : ∀ {m : ℕ}, m ∣ n → m ∣ a → a % n % m = a % m
-- Hmm, this is about mod, not div.

-- Let me try a direct approach
-- v % 3^n / 3^i % 3 = v / 3^i % 3 for i < n

-- Key identity: for 0 < c, c ∣ a → (a + b) / c = a / c + b / c
-- when b < c
#check @Nat.add_div_right

-- Let me just try to prove the digit lemma directly
-- using omega and existing facts

-- The key identity I need is:
-- v / 3^i = (v / 3^n) * 3^(n - i) + (v % 3^n) / 3^i
-- This follows from:
-- v = (v / 3^n) * 3^n + v % 3^n (by Nat.div_add_mod)
-- v / 3^i = ((v / 3^n) * 3^n + v % 3^n) / 3^i
--         = (v / 3^n) * 3^(n-i) + (v % 3^n) / 3^i  [using div_add_div when 3^i | (v/3^n)*3^n]

-- Let me try to prove it
example (v n i : ℕ) (hi : i < n) :
    v / 3^i = (v / 3^n) * 3^(n - i) + v % 3^n / 3^i := by
  have hdvd : 3^i ∣ 3^n := Nat.pow_dvd_pow i (le_of_lt hi)
  have hdvd2 : 3^i ∣ (v / 3^n) * 3^n := by
    constructor
    · use (v / 3^n) * 3^(n - i)
      rw [← Nat.pow_add]
      congr 1
      omega
  rw [show v = (v / 3^n) * 3^n + v % 3^n from (Nat.div_add_mod v (3^n)).symm]
  rw [Nat.add_div_of_dvd_left hdvd2]
  rw [Nat.mul_div_cancel_left (v / 3^n) (by positivity : 0 < 3^i)]
  congr 1
  rw [show 3^n = 3^i * 3^(n - i) from by rw [← Nat.pow_add]; congr 1; omega]
  rw [Nat.mul_div_cancel_left _ (by positivity : 0 < 3^i)]
