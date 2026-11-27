/-
Copyright (c) 2026. All rights reserved.
Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
Authors: Mathematical Research Handoff
-/
import Mathlib
import ErdosTernary.Narkiewicz

/-!
# Base-4 Repunit Coordinates for the Erdős Ternary Problem

This module establishes the exact base-4 repunit reformulation of the Erdős ternary problem:
- Any admissible power of two has an even exponent: $n = 2s$.
- $2^{2s} = 4^s = 3 R_s(4) + 1$, where $R_s(4) = (4^s - 1) / 3$.
- The ternary digits of $4^s$ and $R_s(4)$ satisfy the exact shift:
  $d_0(4^s) = 1$, and $d_{j+1}(4^s) = d_j(R_s(4))$ for all $j ≥ 0$.
- Consequently, $4^s$ omits the ternary digit 2 if and only if $R_s(4)$ omits 2.
-/

namespace ErdosTernary.RepunitBase4

open Narkiewicz

/-- The base-4 generalized repunit: R_s(4) = (4^s - 1) / 3. -/
def repunit4 (s : ℕ) : ℕ :=
  (4 ^ s - 1) / 3

/-- 4^s is 1 mod 3 for all s. -/
theorem pow4_mod_three (s : ℕ) : (4 ^ s) % 3 = 1 := by
  induction s with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    have : (4 ^ n * 4) % 3 = ((4 ^ n % 3) * (4 % 3)) % 3 := Nat.mul_mod _ _ _
    rw [this, ih]

/-- 4^s ≡ 1 mod 3, so 3 divides 4^s - 1. -/
theorem three_dvd_pow4_sub_one (s : ℕ) : 3 ∣ (4 ^ s - 1) := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have hpos : 1 ≤ 4 ^ s := Nat.one_le_pow s 4 (by omega)
  have hmod := pow4_mod_three s
  omega

/-- Exact affine identity: 4^s = 3 * R_s(4) + 1. -/
theorem pow4_eq_three_mul_repunit (s : ℕ) : 4 ^ s = 3 * repunit4 s + 1 := by
  dsimp [repunit4]
  have hdvd := three_dvd_pow4_sub_one s
  have _ := Nat.mul_div_cancel' hdvd
  have hpos : 1 ≤ 4 ^ s := Nat.one_le_pow s 4 (by omega)
  omega

/-- Lowest ternary digit of 4^s is always 1 (never 2). -/
theorem digit3_pow4_zero (s : ℕ) : digit₃ (4 ^ s) 0 = 1 := by
  dsimp [digit₃]
  rw [Nat.div_one]
  exact pow4_mod_three s

/-- Exact ternary digit shift between 4^s and repunit4 s:
    digit₃ (4^s) (j + 1) = digit₃ (repunit4 s) j. -/
theorem digit3_pow4_succ (s j : ℕ) :
    digit₃ (4 ^ s) (j + 1) = digit₃ (repunit4 s) j := by
  dsimp [digit₃]
  have h_aff := pow4_eq_three_mul_repunit s
  have h_div3 : 4 ^ s / 3 = repunit4 s := by
    rw [h_aff]
    omega
  have h_pow : 3 ^ (j + 1) = 3 * 3 ^ j := by
    rw [pow_succ]
    ring
  rw [h_pow, ← Nat.div_div_eq_div_mul, h_div3]

/-- A power of two with even exponent 4^s omits digit 2 in base 3
    if and only if its base-4 repunit R_s(4) omits digit 2 in base 3. -/
theorem memCantorNat_pow4_iff_memCantorNat_repunit (s : ℕ) :
    memCantorNat (4 ^ s) ↔ memCantorNat (repunit4 s) := by
  rw [memCantorNat, memCantorNat]
  constructor
  · intro h j
    have hj1 := h (j + 1)
    rwa [digit3_pow4_succ] at hj1
  · intro h k
    rcases k with _ | j
    · rw [digit3_pow4_zero]; decide
    · rw [digit3_pow4_succ]
      exact h j

/-- For odd exponents n = 2s + 1, the lowest ternary digit is always 2. -/
theorem digit3_pow2_odd_zero (s : ℕ) : digit₃ (2 ^ (2 * s + 1)) 0 = 2 := by
  dsimp [digit₃]
  rw [Nat.div_one]
  have : 2 ^ (2 * s + 1) = 2 * (2 ^ 2) ^ s := by
    rw [pow_succ, pow_mul]
    ring
  have h4 : 2 ^ 2 = 4 := rfl
  rw [this, h4]
  have : (2 * 4 ^ s) % 3 = ((2 % 3) * (4 ^ s % 3)) % 3 := Nat.mul_mod _ _ _
  rw [this, pow4_mod_three s]

/-- Odd powers of two are NEVER in the Cantor set. -/
theorem not_memCantorNat_pow2_odd (s : ℕ) : ¬ memCantorNat (2 ^ (2 * s + 1)) := by
  intro h
  have h0 := h 0
  have h_d0 := digit3_pow2_odd_zero s
  contradiction

end ErdosTernary.RepunitBase4
