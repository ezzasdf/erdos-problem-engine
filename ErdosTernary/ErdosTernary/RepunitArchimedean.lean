/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathematical Research Handoff
-/
import Mathlib
import ErdosTernary.Narkiewicz
import ErdosTernary.RepunitBase4

namespace ErdosTernary.RepunitArchimedean

open Narkiewicz
open ErdosTernary.RepunitBase4

/-- Helper for 5 + k: 3^(5 + k + 1) < 4^(5 + k). -/
theorem four_pow_gt_three_pow_succ_add (k : ℕ) : 3 ^ (5 + k + 1) < 4 ^ (5 + k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : 3 ^ (5 + (k + 1) + 1) = 3 ^ (5 + k + 1) * 3 := by
      have : 5 + (k + 1) + 1 = (5 + k + 1) + 1 := by omega
      rw [this, pow_succ]
    have h2 : 4 ^ (5 + (k + 1)) = 4 ^ (5 + k) * 4 := by
      have : 5 + (k + 1) = (5 + k) + 1 := by omega
      rw [this, pow_succ]
    rw [h1, h2]
    have h3 : 3 ^ (5 + k + 1) * 3 < 4 ^ (5 + k) * 3 := Nat.mul_lt_mul_of_pos_right ih (by omega)
    have hpos : 0 < 4 ^ (5 + k) := Nat.pow_pos (by omega)
    have h4 : 4 ^ (5 + k) * 3 < 4 ^ (5 + k) * 4 := Nat.mul_lt_mul_of_pos_left (by omega) hpos
    exact lt_trans h3 h4

/-- For s ≥ 5, 4^s strictly exceeds 3^(s+1). -/
theorem four_pow_gt_three_pow_succ (s : ℕ) (hs : 5 ≤ s) : 3 ^ (s + 1) < 4 ^ s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact four_pow_gt_three_pow_succ_add k

/-- For s ≥ 5, the base-4 repunit R_s(4) is at least 3^s. -/
theorem repunit4_ge_three_pow (s : ℕ) (hs : 5 ≤ s) : 3 ^ s ≤ repunit4 s := by
  have h_gt := four_pow_gt_three_pow_succ s hs
  have h_aff := pow4_eq_three_mul_repunit s
  have h_pow : 3 ^ (s + 1) = 3 * 3 ^ s := by
    rw [pow_succ]
    ring
  rw [h_aff, h_pow] at h_gt
  omega

/-- For s ≥ 5, the Archimedean quotient R_s(4) / 3^s is strictly positive. -/
theorem repunit4_div_three_pow_pos (s : ℕ) (hs : 5 ≤ s) : 0 < repunit4 s / 3 ^ s := by
  have h_ge := repunit4_ge_three_pow s hs
  have h_ne : 3 ^ s ≠ 0 := by positivity
  exact (Nat.div_pos_iff h_ne).mpr h_ge

/-- Decoupling lemma: A natural number n belongs to the Cantor set iff
    its first s ternary digits omit 2 AND the high-order quotient n / 3^s belongs to the Cantor set. -/
theorem cantor_nat_iff_low_and_high (n s : ℕ) :
    memCantorNat n ↔ (∀ j < s, digit₃ n j ≠ 2) ∧ memCantorNat (n / 3 ^ s) := by
  constructor
  · intro hn
    constructor
    · intro j _
      exact hn j
    · intro k
      rw [digit₃_div_pow]
      exact hn (s + k)
  · rintro ⟨hlow, hhigh⟩ k
    by_cases hk : k < s
    · exact hlow k hk
    · have : s ≤ k := by omega
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le this
      rw [← digit₃_div_pow]
      exact hhigh j

/-- The repunit R_s(4) belongs to the Cantor set iff its adic prefix omits 2
    and its Archimedean quotient R_s(4) / 3^s belongs to the Cantor set. -/
theorem memCantorNat_repunit_iff_adic_and_archimedean (s : ℕ) :
    memCantorNat (repunit4 s) ↔
    (∀ j < s, digit₃ (repunit4 s) j ≠ 2) ∧ memCantorNat (repunit4 s / 3 ^ s) :=
  cantor_nat_iff_low_and_high (repunit4 s) s

/-- 4^s belongs to the Cantor set iff its adic prefix omits 2
    and its Archimedean quotient R_s(4) / 3^s belongs to the Cantor set. -/
theorem memCantorNat_pow4_iff_adic_and_archimedean (s : ℕ) :
    memCantorNat (4 ^ s) ↔
    (∀ j < s, digit₃ (repunit4 s) j ≠ 2) ∧ memCantorNat (repunit4 s / 3 ^ s) := by
  rw [memCantorNat_pow4_iff_memCantorNat_repunit, memCantorNat_repunit_iff_adic_and_archimedean]

/-- 4^0 = 1 belongs to the Cantor set. -/
theorem four_pow_zero_mem_cantor : memCantorNat (4 ^ 0) := one_mem_cantor

/-- 4^1 = 4 belongs to the Cantor set. -/
theorem four_pow_one_mem_cantor : memCantorNat (4 ^ 1) := four_mem_cantor

/-- 4^4 = 256 belongs to the Cantor set. -/
theorem four_pow_four_mem_cantor : memCantorNat (4 ^ 4) := by
  intro k
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | k + 6 =>
    dsimp [digit₃]
    have h_pow : 256 < 3 ^ (k + 6) := by
      have : 3 ^ 6 ≤ 3 ^ (k + 6) := Nat.pow_le_pow_right (by omega) (by omega)
      have : 3 ^ 6 = 729 := by decide
      omega
    have h_div : 256 / 3 ^ (k + 6) = 0 := (Nat.div_eq_zero_iff (Nat.pow_pos (by omega))).mpr h_pow
    rw [h_div]
    decide

/-- 4^2 = 16 does NOT belong to the Cantor set (digit 1 is 2). -/
theorem not_memCantorNat_four_pow_two : ¬ memCantorNat (4 ^ 2) := by
  intro h
  have h1 := h 1
  revert h1
  decide

/-- 4^3 = 64 does NOT belong to the Cantor set (digit 3 is 2). -/
theorem not_memCantorNat_four_pow_three : ¬ memCantorNat (4 ^ 3) := by
  intro h
  have h3 := h 3
  revert h3
  decide

/-- Non-Circular Reduction of the Erdős Ternary Problem:
    For any exponent s ∈ ℕ:
    4^s belongs to the Cantor set if and only if:
    - s ∈ {0, 1, 4}, OR
    - s ≥ 5, s survives to depth s in the repunit tree, AND the Archimedean quotient R_s(4) / 3^s belongs to the Cantor set.
-/
theorem erdos_ternary_reduction (s : ℕ) :
    memCantorNat (4 ^ s) ↔
    (s = 0 ∨ s = 1 ∨ s = 4) ∨
    (5 ≤ s ∧ (∀ j < s, digit₃ (repunit4 s) j ≠ 2) ∧ memCantorNat (repunit4 s / 3 ^ s)) := by
  constructor
  · intro h
    by_cases hs5 : 5 ≤ s
    · right
      refine ⟨hs5, ?_⟩
      rwa [← memCantorNat_pow4_iff_adic_and_archimedean]
    · left
      interval_cases s
      · left; rfl
      · right; left; rfl
      · exfalso; exact not_memCantorNat_four_pow_two h
      · exfalso; exact not_memCantorNat_four_pow_three h
      · right; right; rfl
  · rintro (h0 | ⟨_, hlow, hhigh⟩)
    · rcases h0 with rfl | rfl | rfl
      · exact four_pow_zero_mem_cantor
      · exact four_pow_one_mem_cantor
      · exact four_pow_four_mem_cantor
    · rw [memCantorNat_pow4_iff_adic_and_archimedean]
      exact ⟨hlow, hhigh⟩

end ErdosTernary.RepunitArchimedean
