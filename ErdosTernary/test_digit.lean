import Mathlib.Tactic

-- Try to find the right lemma
#check @Nat.div_mod_mod

-- Alternative: try the proof directly
example (v n i : ℕ) (hi : i < n) : v % 3^n / 3^i % 3 = v / 3^i % 3 := by
  have h1 := Nat.div_add_mod v (3^n)
  have h2 : 3^n = 3^i * 3^(n-i) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [h2] at h1
  -- h1 : v / (3^i * 3^(n-i)) * (3^i * 3^(n-i)) + v % (3^i * 3^(n-i)) = v
  rw [show v = v / (3^i * 3^(n-i)) * (3^i * 3^(n-i)) + v % (3^i * 3^(n-i)) from h1.symm]
  rw [Nat.add_div (by positivity : 0 < 3^i)]
  sorry
