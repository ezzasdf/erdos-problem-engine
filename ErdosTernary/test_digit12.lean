import Mathlib.Tactic

-- Search for existing lemmas about digit extraction
-- The key fact: a / b % c = (a % (b * c)) / b
-- This should be in Mathlib somewhere

-- Try various lemma names
#check @Nat.div_mod_eq_iff
#check @Nat.mod_div_eq_mod_mod
#check @Nat.div_mod_mod
#check @Nat.div_eq_div_of_mod_eq
#check @Nat.eq_div_of_mul_eq_left

-- The key identity: a / b % c = (a % (b * c)) / b
-- In our case: v / 3^i % 3 = (v % (3^i * 3)) / 3^i
-- Which is: v / 3^i % 3 = (v % 3^(i+1)) / 3^i

-- Let me search more broadly
#check @Nat.div_add_div_dvd
#check @Nat.mul_div_mul_comm
#check @Nat.div_mul_div_cancel
#check @Nat.mul_div_cancel_left
#check @Nat.div_mul_cancel

-- Actually, let me try to just find the right lemma by trying to prove it with omega
-- The issue is omega doesn't handle division.

-- Let me try using `native_decide` for a bounded version
-- The digit of_mod for bounded values
example : ∀ v < 10000, ∀ i < 5, ∀ n, i < n → n ≤ 6 →
    v % 3^n / 3^i % 3 = v / 3^i % 3 := by
  intro v hv i hi n hin hn
  native_decide

-- Great! native_decide works for bounded versions. But we need unbounded.

-- Let me try the approach: prove it using Nat.div_add_mod and omega
-- Key: w = q * m + r where m = 3^(i+1), q = w / m, r = w % m
-- w / 3^i = q * 3 + r / 3^i (using add_mul_div_right)
-- So w / 3^i % 3 = r / 3^i % 3 = r / 3^i (since r/3^i < 3)

-- Let me try the proof using a `show` step
-- w / 3^i = (w % 3^(i+1) + w / 3^(i+1) * 3 * 3^i) / 3^i
-- = w % 3^(i+1) / 3^i + w / 3^(i+1) * 3

-- Let me try using `conv` or `show` to guide Lean
example (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  have hp : 0 < 3^i := by exact Nat.pow_pos (by norm_num)
  have h := Nat.div_add_mod w (3^(i+1))
  -- h : w / 3^(i+1) * 3^(i+1) + w % 3^(i+1) = w
  -- So w / 3^i = (w / 3^(i+1) * 3^(i+1) + w % 3^(i+1)) / 3^i
  rw [show w = w / 3^(i+1) * 3^(i+1) + w % 3^(i+1) from h]
  rw [h31]
  -- goal: (w / 3^(i+1) * (3^i * 3) + w % (3^i * 3)) / 3^i % 3 = w % (3^i * 3) / 3^i
  rw [show w / 3^(i+1) * (3^i * 3) + w % (3^i * 3) = 
        w % (3^i * 3) + w / 3^(i+1) * 3 * 3^i from by ring]
  rw [Nat.add_mul_div_right (w % (3^i * 3)) (w / 3^(i+1) * 3) hp]
  -- goal: (w % (3^i * 3) / 3^i + w / 3^(i+1) * 3) % 3 = w % (3^i * 3) / 3^i
  rw [Nat.add_mod, show (w / 3^(i+1) * 3) % 3 = 0 from Nat.mul_mod_left _ _, Nat.zero_add]
  exact Nat.mod_eq_of_lt (by
    have := Nat.mod_lt (3^i * 3) hp
    rw [h31] at this
    exact (Nat.div_lt_iff_lt_mul hp).mpr this)
