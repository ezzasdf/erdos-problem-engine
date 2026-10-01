import Mathlib.Tactic

-- Search for relevant lemmas
#check @Nat.div_div_eq_div_mul
#check @Nat.mod_div_div_mod
#check @Nat.div_mod_eq_iff
#check @Nat.eq_div_of_mul_eq_left
#check @Nat.mod_self

-- Try the approach: (v % 3^n) / 3^i = v / 3^i % 3^(n-i)
-- This follows from: v / 3^i = (v / 3^n) * 3^(n-i) + (v % 3^n) / 3^i
-- and (v % 3^n) / 3^i < 3^(n-i)
-- so (v / 3^i) % 3^(n-i) = (v % 3^n) / 3^i

-- Then ((v % 3^n) / 3^i) % 3 = (v / 3^i % 3^(n-i)) % 3 = (v / 3^i) % 3
-- because a % 3^m % 3 = a % 3 when m ≥ 1

-- Let me try a direct approach using omega
example (v n i : ℕ) (hi : i < n) : v % 3^n / 3^i % 3 = v / 3^i % 3 := by
  -- Use the fact that v = (v / 3^n) * 3^n + v % 3^n
  have h := Nat.div_add_mod v (3^n)
  -- Rewrite 3^n as 3^i * 3^(n-i)
  have hpow : 3^n = 3^i * 3^(n-i) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hpow] at h
  -- Now h : v / (3^i * 3^(n-i)) * (3^i * 3^(n-i)) + v % (3^i * 3^(n-i)) = v
  -- We want to show v % (3^i * 3^(n-i)) / 3^i % 3 = v / 3^i % 3
  -- Key: v / 3^i = (v / (3^i * 3^(n-i))) * 3^(n-i) + (v % (3^i * 3^(n-i))) / 3^i
  have hdiv : v / 3^i = v / (3^i * 3^(n-i)) * 3^(n-i) + v % (3^i * 3^(n-i)) / 3^i := by
    have h2 := Nat.div_add_div (v % (3^i * 3^(n-i))) (by omega)
    sorry
  sorry
