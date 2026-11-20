/-
Copyright (c) 2026 The ErdosTernary Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The ErdosTernary Contributors
-/
import Mathlib
import ErdosTernary.RepunitCarryPacket

/-!
# Negative-Power Erdős Analogue and the Gap Lemma

This module formalizes the negative-power analogue of the Erdős ternary problem:
1. **The Gap Lemma:** The coset of odd residues congruent to 1 or 3 modulo 8 has
   maximum gap strictly bounded by 6. Consequently, every integer interval of length
   at least 6 contains an element of this coset.
2. **The Target Interval:** For any reciprocal $1/2^n$ in base 3, a residue $x \in [0, 2^n)$
   generates digit 2 if and only if $3x / 2^n \ge 2$, i.e., $x \ge \text{threshold } n$.
3. **The Negative-Power Theorem:** For all $n \ge 5$, the target interval has length
   greater than 6, guaranteeing the presence of a residue in the coset.
   Combined with explicit verification for small $n$, the only exponents where $1/2^n$
   omits digit 2 are $n = 1$ ($1/2 = 0.111\dots_3$) and $n = 3$ ($1/8 = 0.0101\dots_3$).
-/

namespace ErdosTernary.NegativePower

open ErdosTernary.RepunitCarryPacket

/-- The coset of odd residues congruent to 1 or 3 modulo 8. -/
def isCoset13 (x : ℕ) : Prop :=
  x % 8 = 1 ∨ x % 8 = 3

/-- Gap Lemma (local): In any block of 7 consecutive integers {a, a+1, ..., a+6},
    at least one integer belongs to the coset {1, 3} mod 8. -/
theorem exists_coset13_in_range_seven (a : ℕ) : ∃ i ≤ 6, isCoset13 (a + i) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ a = 8 * q + r :=
    ⟨a / 8, a % 8, Nat.mod_lt _ (by decide), (Nat.div_add_mod a 8).symm⟩
  interval_cases r
  · use 1; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 0 + 1) % 8 = 1 := by omega
    left; exact this
  · use 0; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 1 + 0) % 8 = 1 := by omega
    left; exact this
  · use 1; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 2 + 1) % 8 = 3 := by omega
    right; exact this
  · use 0; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 3 + 0) % 8 = 3 := by omega
    right; exact this
  · use 5; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 4 + 5) % 8 = 1 := by omega
    left; exact this
  · use 4; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 5 + 4) % 8 = 1 := by omega
    left; exact this
  · use 3; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 6 + 3) % 8 = 1 := by omega
    left; exact this
  · use 2; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 7 + 2) % 8 = 1 := by omega
    left; exact this

/-- Gap Lemma (interval): Any interval [A, B] of length at least 6 contains
    an element of the coset {1, 3} mod 8. -/
theorem exists_coset13_between {A B : ℕ} (h : A + 6 ≤ B) :
    ∃ x, A ≤ x ∧ x ≤ B ∧ isCoset13 x := by
  obtain ⟨i, hi6, hcoset⟩ := exists_coset13_in_range_seven A
  use A + i
  refine ⟨by omega, by omega, hcoset⟩

/-- The base-3 digit produced by residue x < 2^n in the expansion of 1/2^n. -/
def digit3OfResidue (n x : ℕ) : ℕ :=
  (3 * x) / (2 ^ n)

/-- The lower threshold for residue x to produce digit 2 in base 3:
    3x ≥ 2 · 2^n ↔ x ≥ ⌈(2 · 2^n) / 3⌉. -/
def threshold (n : ℕ) : ℕ :=
  (2 * 2 ^ n + 2) / 3

/-- Any residue in [threshold n, 2^n) forces output digit 2. -/
theorem digit3_eq_two_of_mem_target {n x : ℕ}
    (hx1 : threshold n ≤ x) (hx2 : x < 2 ^ n) :
    digit3OfResidue n x = 2 := by
  dsimp [digit3OfResidue]
  have hpos : 0 < 2 ^ n := by positivity
  have hlower : 2 * 2 ^ n ≤ 3 * x := by
    dsimp [threshold] at hx1
    omega
  have hupper : 3 * x < 3 * 2 ^ n := by omega
  have h1 : 2 ≤ (3 * x) / (2 ^ n) := (Nat.le_div_iff_mul_le hpos).mpr hlower
  have h2 : (3 * x) / (2 ^ n) < 3 := (Nat.div_lt_iff_lt_mul hpos).mpr hupper
  omega

/-- For all n ≥ 5, the target interval [threshold n, 2^n - 1] has width at least 6. -/
theorem threshold_add_six_le_pred_pow2 {n : ℕ} (hn : 5 ≤ n) :
    threshold n + 6 ≤ 2 ^ n - 1 := by
  have h2n : 32 ≤ 2 ^ n := by
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  dsimp [threshold]
  omega

/-- Guaranteed intersection: For all n ≥ 5, the target interval contains an element
    of the coset {1, 3} mod 8. -/
theorem exists_target_residue {n : ℕ} (hn : 5 ≤ n) :
    ∃ x, threshold n ≤ x ∧ x < 2 ^ n ∧ isCoset13 x := by
  have hbound := threshold_add_six_le_pred_pow2 hn
  obtain ⟨x, hA, hB, hcoset⟩ := exists_coset13_between hbound
  refine ⟨x, hA, by omega, hcoset⟩

/-- Small cases: explicit verification that digit 2 appears for n = 2 and n = 4. -/
theorem digit3_two_at_n2 : digit3OfResidue 2 (3 ^ 1 % 4) = 2 := by
  decide

theorem digit3_two_at_n4 : digit3OfResidue 4 (3 ^ 3 % 16) = 2 := by
  decide

/-- Small cases: n = 1 (1/2) and n = 3 (1/8) avoid digit 2. -/
theorem no_digit2_at_n1 (x : ℕ) (hx : x < 2 ^ 1) : digit3OfResidue 1 x ≠ 2 := by
  interval_cases x <;> decide

theorem no_digit2_at_n3 (k : ℕ) : digit3OfResidue 3 (3 ^ k % 8) ≠ 2 := by
  have h3 := pow3_mod8 k
  rcases h3 with h | h
  · dsimp [digit3OfResidue]
    rw [h]; decide
  · dsimp [digit3OfResidue]
    rw [h]; decide

#print axioms exists_coset13_in_range_seven
#print axioms exists_coset13_between
#print axioms digit3_eq_two_of_mem_target
#print axioms threshold_add_six_le_pred_pow2
#print axioms exists_target_residue
#print axioms digit3_two_at_n2
#print axioms digit3_two_at_n4
#print axioms no_digit2_at_n1
#print axioms no_digit2_at_n3

end ErdosTernary.NegativePower
