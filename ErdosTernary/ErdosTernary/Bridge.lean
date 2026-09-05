/-
  Bridge Theorem: Leading/Trailing Orbit Intersection

  Sorry-free: B_K(n) for n = 0, 2, 8; quantitative bound.
  BridgeCompute.lean: K=5..9 proved by native_decide (zero sorry).
  Axioms: bridge theorem, Erdős conjecture (pending full induction proof).

  Key insight (2026-08-21): The bridge theorem for ALL n is false
  (equidistribution shows orbit visits φ⁻¹(C_L) infinitely often).
  But the FIRST-PERIOD result (n ∈ [0, u_K)) is true and sufficient:
  - For n ∈ [0, u_K), verified by native_decide (K=5..9) and
    computational check (K=10..15, bridge_induction_check.py)
  - For n ≥ u_K, Saye recursion ensures intersection of all N_K = {0,2,8}

  Reference: verify_middle/BRIDGE_RIGOROUS_PROOF.md
  Induction check: verify_middle/bridge_induction_check.py
  Computational proofs: ErdosTernary/BridgeCompute.lean
-/

import Mathlib.Tactic
import ErdosTernary.SayeLemma
import ErdosTernary.Narkiewicz

open ErdosTernary.SayeLemma
open Narkiewicz

namespace ErdosTernary.Bridge

/-! ## Part 1: B_K(n) — Trailing 2-free Condition -/

/-- B_K(n): the last K ternary digits of 2^n have no digit 2. -/
def B (K n : ℕ) : Prop :=
  ∀ i < K, digit₃ (2 ^ n % 3 ^ K) i ≠ 2

/-- 2^0 % 3^K = 1 for K ≥ 1. -/
theorem pow_zero_mod (K : ℕ) (hK : K ≥ 1) : 2 ^ 0 % 3 ^ K = 1 := by
  rw [Nat.pow_zero]
  apply Nat.mod_eq_of_lt
  have h3 : 3 ≤ 3 ^ K :=
    Nat.le_trans (by omega : 3 ≤ 3 ^ 1) (Nat.pow_le_pow_right (by omega : 3 > 0) hK)
  omega

/-- 2^2 % 3^K = 4 for K ≥ 2. -/
theorem pow_two_mod (K : ℕ) (hK : K ≥ 2) : 2 ^ 2 % 3 ^ K = 4 := by
  rw [Nat.pow_two]
  apply Nat.mod_eq_of_lt
  have h9 : 3 ^ K ≥ 9 := Nat.pow_le_pow_right (by omega : 3 > 0) hK
  omega

/-- 2^8 % 3^K = 256 for K ≥ 6. -/
theorem pow_eight_mod (K : ℕ) (hK : K ≥ 6) : 2 ^ 8 % 3 ^ K = 256 := by
  apply Nat.mod_eq_of_lt
  have h729 : 3 ^ K ≥ 729 := Nat.pow_le_pow_right (by omega : 3 > 0) hK
  omega

/-- B_K(0): 2^0 = 1 has no digit 2. -/
theorem B_zero (K : ℕ) (hK : K ≥ 1) : B K 0 := by
  intro i hi
  unfold digit₃
  rw [pow_zero_mod K hK]
  by_cases hi0 : i = 0
  · subst hi0; simp [show 1 / 1 = 1 by omega, show 1 % 3 = 1 by omega]
  have hge1 : i ≥ 1 := by omega
  have h3i : 3 ^ i ≥ 3 := Nat.pow_le_pow_right (by omega : 3 > 0) hge1
  have hdiv : 1 / 3 ^ i = 0 := by
    rw [Nat.div_eq_zero_iff (by positivity : 0 < 3 ^ i)]
    omega
  rw [hdiv]; simp

/-- B_K(2): 2^2 = 4 = 11_3 has no digit 2. -/
theorem B_two (K : ℕ) (hK : K ≥ 2) : B K 2 := by
  intro i hi
  unfold digit₃
  rw [pow_two_mod K hK]
  by_cases hi0 : i = 0
  · subst hi0; simp [show 4 / 1 = 4 by omega, show 4 % 3 = 1 by omega]
  by_cases hi1 : i = 1
  · subst hi1; simp [show 4 / 3 = 1 by omega, show 1 % 3 = 1 by omega]
  have hge2 : i ≥ 2 := by omega
  have h3i : 3 ^ i ≥ 9 := Nat.pow_le_pow_right (by omega : 3 > 0) hge2
  have hdiv : 4 / 3 ^ i = 0 := by
    rw [Nat.div_eq_zero_iff (by positivity : 0 < 3 ^ i)]
    omega
  rw [hdiv]; simp

/-- B_K(8): 2^8 = 256 = 100111_3, no digit 2 in positions 0..5.
    For i ≥ 6, digit₃ 256 i = 0. -/
theorem B_eight (K : ℕ) (hK : K ≥ 6) : B K 8 := by
  intro i hi
  unfold digit₃
  rw [pow_eight_mod K hK]
  -- Case split: i < 6 or i ≥ 6
  by_cases hlt6 : i < 6
  · -- Manual case analysis for i = 0..5
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
    · subst h0; simp [show 256 / 1 % 3 = 1 by omega]
    · subst h1; simp [show 256 / 3 % 3 = 1 by omega]
    · subst h2; simp [show 256 / 9 % 3 = 1 by omega]
    · subst h3; simp [show 256 / 27 % 3 = 0 by omega]
    · subst h4; simp [show 256 / 81 % 3 = 0 by omega]
    · subst h5; simp [show 256 / 243 % 3 = 1 by omega]
  · -- For i ≥ 6: 256 < 3^6 ≤ 3^i, so digit₃ 256 i = 0
    have hge6 : i ≥ 6 := by omega
    have h3i : 3 ^ i ≥ 3 ^ 6 := Nat.pow_le_pow_right (by omega : 3 > 0) hge6
    have hdiv : 256 / 3 ^ i = 0 := by
      rw [Nat.div_eq_zero_iff (by positivity : 0 < 3 ^ i)]
      omega
    rw [hdiv]; simp

/-! ## Part 2: Quantitative bridge bound -/

/-- The expected count of extra survivors: |N_K| · (2/3)^L. -/
noncomputable def expectedCount (K L : ℕ) : ℝ :=
  (2 : ℝ) ^ (K - 1) * (2 / 3) ^ L

/-- For K = 5, L = 30: expected ≈ 7.5e-5 < 1. -/
theorem expectedCount_K5_L30 : expectedCount 5 30 < 1 := by
  unfold expectedCount; norm_num

/-- For K = 12, L = 30: expected ≈ 0.0096 < 1. -/
theorem expectedCount_K12_L30 : expectedCount 12 30 < 1 := by
  unfold expectedCount; norm_num

/-- For K = 15, L = 30: expected ≈ 0.077 < 1. -/
theorem expectedCount_K15_L30 : expectedCount 15 30 < 1 := by
  unfold expectedCount; norm_num

/-! ## Part 3: Bridge Theorem (Eliminated) -/

-- The 4 axioms that were here (bridge_theorem, bridge_theorem_first_period,
-- saye_intersection, erdos_conjecture) have been removed.
-- None were used by any theorem in the project. The actual bridge proof uses:
--   BridgeCompute.lean: K=5..9 by native_decide
--   BridgeMiddle.lean: K=10..12 by native_decide on mod 3^50
--   BridgeUniform.lean: K>=13 via ostrowski_invariant axiom
--   BridgeOstrowskiInvariant.lean: re-exports the full result

end ErdosTernary.Bridge
