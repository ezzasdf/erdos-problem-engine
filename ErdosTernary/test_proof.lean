import Mathlib.Tactic
import ErdosTernary.BridgeCompute
import ErdosTernary.Mass1Dynamics

open ErdosTernary.BridgeCompute
open ErdosTernary.OstrowskiFormLemma

-- For j≥10, all mass-1 candidates Q(j)+ℓ (ℓ≤18) are excluded from N_K for K≥10
-- because they all have trailing digit 2 in 2^r mod 3^10
-- and 3^10 | 3^K, so the digit persists for all K≥10

-- Key helper: (2^r % 3^K) % 3^10 = 2^r % 3^10 for K≥10
-- So if 2^r % 3^10 has digit 2 in last 10 digits, so does 2^r % 3^K in last K digits

-- Q(9)+18 < uK 7
private lemma Q9_plus_18_lt_uK7 : Q Al32 9 + 18 < uK 7 := by native_decide

-- For the trailing digit subset: if v has no digit 2 in K digits,
-- then v % 3^(K-1) has no digit 2 in K-1 digits
-- This is because digits 0..K-2 of v%3^(K-1) = digits 0..K-2 of v

-- Approach: prove by showing that for each i < K-1, digit i of v%3^(K-1) = digit i of v

-- Actually, let me think about a cleaner approach...
-- The computeNK definition uses `2^r % modulus` directly, not pow2Mod.
-- So `r ∈ computeNK K` means `r < uK K` and `!(hasTrailingDigit2 (2^r % 3^K) K)`.

-- For r ∈ computeNK (K-1): need `r < uK (K-1)` and `!(hasTrailingDigit2 (2^r % 3^(K-1)) (K-1))`.

-- Key lemma: if !hasTrailingDigit2 (2^r % 3^K) K, then !hasTrailingDigit2 (2^r % 3^(K-1)) (K-1)
-- because the last K-1 ternary digits of (2^r % 3^K) agree with (2^r % 3^(K-1))
-- i.e., (2^r % 3^K) % 3^(K-1) = 2^r % 3^(K-1) and digit extraction agrees

-- For i < n: ((v % 3^n) / 3^i) % 3 = (v / 3^i) % 3
-- This is because v and v%3^n share the same lower n ternary digits

private lemma digit_of_mod (v n i : ℕ) (hi : i < n) :
    ((v % 3^n) / 3^i) % 3 = (v / 3^i) % 3 := by
  have h := Nat.div_add_mod v (3^n)
  rw [show 3^n = 3^i * 3^(n - i) from by rw [← Nat.pow_succ]; congr 1; omega] at h
  have hdiv : 3^i ∣ (v / 3^n) * 3^i * 3^(n - i) := ⟨(v / 3^n) * 3^(n - i), by ring⟩
  rw [mul_assoc] at h
  rw [Nat.add_div_of_dvd_left hdiv] at h
  sorry -- need more work
