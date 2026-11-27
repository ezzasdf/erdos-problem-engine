/-
Copyright (c) 2026. All rights reserved.
Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
Authors: Mathematical Research Handoff
-/
import Mathlib
import ErdosTernary.Narkiewicz
import ErdosTernary.RepunitBase4
import ErdosTernary.RepunitLifting

/-!
# Rooted Tree Isomorphism: Repunit Tree ≅ Power-of-Two Survivor Tree

This module proves the exact isomorphism between:
1. The Repunit Survivor Tree $\mathcal{T}_{\text{rep}}$:
   Nodes at level $m$: indices $s < 3^m$ such that digit₃ (repunit4 s) j ≠ 2 for all j < m.
2. The Power-of-Two Survivor Tree $\mathcal{T}_{\text{pow}}$:
   Nodes at level $K = m + 1$: exponents $n < 2 \cdot 3^m$ such that digit₃ (2^n) j ≠ 2 for all j < m + 1.

The isomorphism is given by:
- Vertex map: $n = 2s$.
- Edge/branching map: Child label $q ∈ \{0, 1, 2\}$ lifts $s \mapsto s + q \cdot 3^m$ in $\mathcal{T}_{\text{rep}}$
  if and only if it lifts $n \mapsto n + 2q \cdot 3^m$ in $\mathcal{T}_{\text{pow}}$.
-/

namespace ErdosTernary.RepunitTreeIso

open Narkiewicz
open ErdosTernary.RepunitBase4
open ErdosTernary.RepunitLifting

/-- A node in the repunit tree at depth m: an index s < 3^m whose repunit
    omits digit 2 in its first m ternary digits. -/
def isRepunitSurvivor (m : ℕ) (s : ℕ) : Prop :=
  s < 3 ^ m ∧ ∀ j < m, digit₃ (repunit4 s) j ≠ 2

/-- A node in the power-of-two survivor tree at depth K: an exponent n < 2 * 3^(K-1)
    whose power 2^n omits digit 2 in its first K ternary digits. -/
def isPowerTwoSurvivor (K : ℕ) (n : ℕ) : Prop :=
  n < 2 * 3 ^ (K - 1) ∧ ∀ j < K, digit₃ (2 ^ n) j ≠ 2

/-- Level 0 equivalence: At depth m = 0 (K = 1), the unique node is s = 0 and n = 0. -/
theorem level0_survivor_equiv :
    isRepunitSurvivor 0 0 ∧ isPowerTwoSurvivor 1 0 := by
  constructor
  · refine ⟨by decide, fun j hj => by omega⟩
  · refine ⟨by decide, fun j hj => ?_⟩
    have : j = 0 := by omega
    subst this
    dsimp [digit₃]
    decide

/-- Parity constraint: Every power-of-two survivor has an even exponent n = 2s. -/
theorem powerTwoSurvivor_even {K n : ℕ} (hK : 1 ≤ K) (h : isPowerTwoSurvivor K n) :
    ∃ s, n = 2 * s := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · exact ⟨n / 2, by omega⟩
  · exfalso
    have : ∃ s, n = 2 * s + 1 := ⟨n / 2, by omega⟩
    rcases this with ⟨s, rfl⟩
    have hd0 := digit3_pow2_odd_zero s
    have hnot := h.2 0 (by omega)
    exact hnot hd0

/-- Vertex Isomorphism at level m (K = m + 1):
    n is a survivor at depth m + 1 iff n = 2s where s is a survivor at depth m. -/
theorem survivor_vertex_equiv (m : ℕ) (n : ℕ) :
    isPowerTwoSurvivor (m + 1) n ↔ ∃ s, n = 2 * s ∧ isRepunitSurvivor m s := by
  constructor
  · intro h
    have ⟨s, h_even⟩ := powerTwoSurvivor_even (by omega) h
    subst h_even
    refine ⟨s, rfl, ?_⟩
    constructor
    · have hn := h.1
      dsimp at hn
      omega
    · intro j hj
      have hj1 : j + 1 < m + 1 := by omega
      have hnot := h.2 (j + 1) hj1
      have h4s : 2 ^ (2 * s) = 4 ^ s := by
        rw [pow_mul]
        rfl
      rw [h4s] at hnot
      rw [digit3_pow4_succ] at hnot
      exact hnot
  · rintro ⟨s, rfl, hs⟩
    constructor
    · dsimp
      have hs1 := hs.1
      omega
    · intro j hj
      have h4s : 2 ^ (2 * s) = 4 ^ s := by
        rw [pow_mul]
        rfl
      rw [h4s]
      rcases j with _ | j
      · rw [digit3_pow4_zero]; decide
      · rw [digit3_pow4_succ]
        apply hs.2
        omega

/-- Branching / Edge Isomorphism:
    For any node s at depth m and child label q ∈ {0, 1, 2},
    s + q * 3^m is admissible in the repunit tree
    if and only if
    2 * s + 2 * q * 3^m is admissible in the power-of-two survivor tree. -/
theorem branching_isomorphism (m s q : ℕ) :
    isRepunitSurvivor (m + 1) (s + q * 3 ^ m) ↔
    isPowerTwoSurvivor (m + 2) (2 * s + 2 * q * 3 ^ m) := by
  have : 2 * s + 2 * q * 3 ^ m = 2 * (s + q * 3 ^ m) := by ring
  rw [this]
  have h_equiv := (survivor_vertex_equiv (m + 1) (2 * (s + q * 3 ^ m))).symm
  constructor
  · intro hs
    exact h_equiv.mp ⟨s + q * 3 ^ m, rfl, hs⟩
  · intro hp
    have ⟨s', heq, hs'⟩ := h_equiv.mpr hp
    have : s' = s + q * 3 ^ m := by omega
    subst this
    exact hs'

end ErdosTernary.RepunitTreeIso
