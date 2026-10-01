import Mathlib.Tactic

-- Simpler approach: prove div_mod_eq
-- w / 3^i % 3 = w % 3^(i+1) / 3^i

-- Step 1: show w % 3^(i+1) / 3^i < 3
private lemma mod_pow_lt (w i : ℕ) : w % 3^(i+1) / 3^i < 3 := by
  have h1 : w % 3^(i+1) < 3^(i+1) := Nat.mod_lt _ (by positivity)
  have h2 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  rw [h2] at h1
  exact Nat.div_lt_iff_lt_mul.mpr h1

-- Step 2: prove div_mod_eq using Nat.add_mul_div_right
-- Key: w = (w % 3^(i+1)) + (w / 3^(i+1)) * 3^i * 3
-- So w / 3^i = (w % 3^(i+1)) / 3^i + (w / 3^(i+1)) * 3
-- So w / 3^i % 3 = (w % 3^(i+1)) / 3^i  [since the second term is divisible by 3]
private lemma div_mod_eq (w i : ℕ) : w / 3^i % 3 = w % 3^(i+1) / 3^i := by
  have h31 : 3^(i+1) = 3^i * 3 := by rw [Nat.pow_succ]; ring
  have h := Nat.div_add_mod w (3^(i+1))
  rw [h31] at h
  -- h : w / (3^i * 3) * (3^i * 3) + w % (3^i * 3) = w
  -- w = w % (3^i * 3) + w / (3^i * 3) * 3^i * 3
  have hdiv : w / 3^i = w % (3^i * 3) / 3^i + w / (3^i * 3) * 3 := by
    rw [← h]
    rw [Nat.add_mul_div_right _ (by positivity : 0 < 3^i)]
    ring_nf
  rw [hdiv, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
  apply Nat.mod_eq_of_lt
  exact mod_pow_lt w i

-- Step 3: prove the digit equality for mod
-- (v % 3^n) / 3^i % 3 = v / 3^i % 3 when i < n
private lemma digit_of_mod (v n i : ℕ) (hi : i < n) :
    (v % 3^n) / 3^i % 3 = v / 3^i % 3 := by
  -- Both sides equal (v % 3^(i+1)) / 3^i
  rw [div_mod_eq, ← div_mod_eq]
  -- Now need: (v % 3^n) % 3^(i+1) / 3^i = v % 3^(i+1) / 3^i
  congr 1
  -- Need: (v % 3^n) % 3^(i+1) = v % 3^(i+1)
  rw [Nat.mod_mod_of_dvd]
  -- Need: 3^(i+1) ∣ 3^n
  exact Nat.pow_dvd_pow _ (by omega : i + 1 ≤ n)

-- Step 4: trailing digit subset
-- If hasTrailingDigit2 v K = false then hasTrailingDigit2 (v % 3^(K-1)) (K-1) = false
private lemma trail_subset (v K : ℕ) (hK : K ≥ 1) :
    hasTrailingDigit2 v K = false → hasTrailingDigit2 (v % 3^(K-1)) (K-1) = false := by
  intro h
  unfold hasTrailingDigit2 at h ⊢
  simp only [Bool.not_eq_false] at h ⊢
  rw [List.any_eq_true] at h ⊢
  intro ⟨i, hi_range, hi_eq⟩
  rw [List.mem_range] at hi_range
  have hi_lt : i < K - 1 := hi_range
  -- Get contradiction from h
  rw [List.any_eq_false] at h
  have h2 : ∀ j < K, (v / 3^j) % 3 ≠ 2 := by
    intro j hj
    intro heq
    exact h ⟨j, List.mem_range.mpr (by omega), by
      simp only [bne_iff_ne, ne_eq] at heq ⊢
      exact heq⟩
  -- We have i < K - 1 < K, and (v % 3^(K-1)) / 3^i % 3 = v / 3^i % 3
  rw [bne_iff_ne] at hi_eq
  apply hi_eq
  rw [digit_of_mod v (K-1) i (by omega)]
  exact h2 i (by omega)
