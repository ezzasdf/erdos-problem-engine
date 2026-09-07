-- Lifting structure theorem for N_K
-- Key identity: 2^(uK K) ≡ 1 + 3^K mod 3^(K+1)
--
-- This file formalizes the algebraic proof that:
-- 1. |N_K| = 2^{K-1} (exponential growth)
-- 2. Exactly two of {r, r+uK, r+2uK} survive into N_{K+1}
-- 3. {0, 2, 8} are the only elements with no digit 2 ever

import Mathlib.Tactic
import ErdosTernary.BridgeCompute

open ErdosTernary.BridgeCompute

namespace ErdosTernary.Lifting

-- ============================================================
-- Phase 1: Core Algebraic Identity
-- ============================================================

/-- The K-th ternary digit of a natural number -/
def ternaryDigit (n k : Nat) : Nat :=
  (n / 3 ^ k) % 3

/-- v_3(n): the 3-adic valuation of n -/
def v3 : Nat → Nat
  | 0 => 0
  | n =>
    if h : n % 3 = 0 then
      1 + v3 (n / 3)
    else 0

/-- Lemma: v_3(3^K) = K -/
theorem v3_pow3 (K : Nat) : v3 (3 ^ K) = K := by
  induction K with
  | zero => simp [v3]
  | succ K ih =>
    rw [Nat.pow_succ, Nat.mul_comm]
    simp [v3, Nat.mul_mod_right]
    rw [ih]

/-- Lemma: v_3(2^2 - 1) = 1, since 2^2 - 1 = 3 -/
theorem v3_three : v3 3 = 1 := by
  simp [v3, Nat.one_lt_iff_ne_zero, Nat.mod_self]

/-- Key identity: 2^(uK K) ≡ 1 + 3^K mod 3^(K+1) -/
-- Proof strategy: induction on K using LTE
theorem pow2_uK_mod (K : Nat) (hK : K ≥ 1) :
    2 ^ uK K % 3 ^ (K + 1) = 1 + 3 ^ K := by
  -- The proof uses the lifting-the-exponent lemma:
  -- v_3(2^{2·3^{K-1}} - 1) = v_3(2^2 - 1) + v_3(3^{K-1}) = 1 + (K-1) = K
  -- So 2^{uK K} = 1 + 3^K (mod 3^{K+1})
  sorry

-- ============================================================
-- Phase 2: Exactly-Two-Lifts (from Phase 1)
-- ============================================================

/-- The K-th ternary digit of 2^(r + j·uK K) -/
def kthDigit (K r j : Nat) : Nat :=
  ternaryDigit (2 ^ (r + j * uK K)) K

/-- If r ∈ N_K, then 2^r mod 3 is not 2 -/
theorem mod3_ne2_of_mem_nk (K r : Nat) (hK : K ≥ 1) (hr : r ∈ computeNKFast K) :
    2 ^ r % 3 ≠ 2 := by
  -- Since r ∈ N_K, 2^r mod 3^K has no digit 2
  -- In particular, the 0-th digit (2^r mod 3) is not 2
  sorry

/-- The three K-th digits form an arithmetic progression with nonzero common difference -/
theorem digits_arithmetic_progression (K r : Nat) (hK : K ≥ 1) (hr : r ∈ computeNKFast K) :
    let d₀ := kthDigit K r 0
    let d₁ := kthDigit K r 1
    let d₂ := kthDigit K r 2
    let a := 2 ^ r % 3 ^ K  -- lower part
    let Δ := a % 3  -- common difference (nonzero)
    d₀ = (2 ^ r % 3 ^ (K + 1) / 3 ^ K) % 3 ∧
    d₁ = (d₀ + Δ) % 3 ∧
    d₂ = (d₀ + 2 * Δ) % 3 ∧
    Δ ≠ 0 := by
  sorry

/-- Exactly one of the three lifts has digit 2 at position K -/
theorem exactly_one_digit2 (K r : Nat) (hK : K ≥ 1) (hr : r ∈ computeNKFast K) :
    let d₀ := kthDigit K r 0
    let d₁ := kthDigit K r 1
    let d₂ := kthDigit K r 2
    (d₀ == 2) + (d₁ == 2) + (d₂ == 2) = 1 := by
  -- From digits_arithmetic_progression:
  -- d₀, d₁, d₂ = b, b+Δ, b+2Δ (mod 3) with Δ ≢ 0 (mod 3)
  -- These are three distinct values mod 3, hence exactly {0,1,2}
  -- So exactly one equals 2
  sorry

/-- Exactly two of the three lifts belong to N_(K+1) -/
theorem exactly_two_lifts (K r : Nat) (hK : K ≥ 1) (hr : r ∈ computeNKFast K) :
    let lifts := [r, r + uK K, r + 2 * uK K]
    let in_next := lifts.filter fun x => x ∈ computeNKFast (K + 1)
    in_next.length = 2 := by
  -- From exactly_one_digit2: exactly one lift has digit 2 at position K
  -- The other two have no digit 2 at position K
  -- Since r ∈ N_K, all three have no digit 2 in positions 0..K-1
  -- So exactly two lifts have no digit 2 in positions 0..K, hence are in N_{K+1}
  sorry

-- ============================================================
-- Phase 3: Exponential Growth (from Phase 2)
-- ============================================================

/-- |N_1| = 1 -/
theorem nk_one : (computeNKFast 1).card = 1 := by
  -- N_1 = {r ∈ [0, 2) : 2^r mod 3 ≠ 2}
  -- 2^0 mod 3 = 1 ✓, 2^1 mod 3 = 2 ✗
  -- So N_1 = {0}, |N_1| = 1
  sorry

/-- |N_K| = 2^{K-1} for all K ≥ 1 -/
theorem nk_size (K : Nat) (hK : K ≥ 1) :
    (computeNKFast K).card = 2 ^ (K - 1) := by
  induction K with
  | zero => contradiction
  | succ K ih =>
    have hK' : K ≥ 1 := by omega
    rw [nk_size K hK']
    -- Use exactly_two_lifts to show |N_{K+1}| = 2 * |N_K|
    sorry

-- ============================================================
-- Phase 4: {0,2,8} Characterization
-- ============================================================

/-- 2^0 = 1 has no digit 2 in any position -/
theorem two_pow_zero_no_digit2 :
    ∀ p, ternaryDigit (2 ^ 0) p ≠ 2 := by
  intro p
  simp [ternaryDigit, Nat.pow_zero, Nat.one_div]
  -- 2^0 = 1, ternaryDigit 1 p is 0 or 1, never 2
  sorry

/-- 2^2 = 4 = 11_3 has no digit 2 in any position -/
theorem two_pow_two_no_digit2 :
    ∀ p, ternaryDigit (2 ^ 2) p ≠ 2 := by
  intro p
  simp [ternaryDigit, Nat.pow_two]
  -- 2^2 = 4, ternary digits: 1, 1, 0, 0, ...
  sorry

/-- 2^8 = 256 = 100111_3 has no digit 2 in any position -/
theorem two_pow_eight_no_digit2 :
    ∀ p, ternaryDigit (2 ^ 8) p ≠ 2 := by
  intro p
  simp [ternaryDigit]
  -- 2^8 = 256, ternary: 1, 0, 0, 1, 1, 1, 0, 0, ...
  sorry

-- ============================================================
-- Phase 5: Bounded Digit-2 Offset (for K ≤ 17)
-- ============================================================

/-- For K = 5..17, every non-special r ∈ N_K has digit 2 in positions K..K+27 -/
theorem bounded_digit2_offset (K r : Nat)
    (hK : 5 ≤ K) (hK' : K ≤ 17)
    (hr : r ∈ computeNKFast K)
    (h_special : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ∃ p, K ≤ p ∧ p ≤ K + 27 ∧
    ternaryDigit (2 ^ r) p = 2 := by
  -- Proof by case analysis on K (finite check for K=5..17)
  -- Each case verified computationally
  sorry

-- ============================================================
-- Phase 6: ostrowski_invariant for K ≤ 17
-- ============================================================

/-- For K ≤ 17, the bridge property holds -/
theorem ostrowski_invariant_le17 (K : Nat) (hK : 5 ≤ K) (hK' : K ≤ 17) :
    checkBridgeCantorPow2 K = true := by
  -- From bounded_digit2_offset: digit 2 at position p ≤ K+27 ≤ 44 ≤ 49
  -- So the bridge property holds
  sorry

end ErdosTernary.Lifting
