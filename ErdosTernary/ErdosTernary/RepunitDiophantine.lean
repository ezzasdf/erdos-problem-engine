/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathematical Research Handoff
-/
import Mathlib
import ErdosTernary.Narkiewicz
import ErdosTernary.RepunitBase4
import ErdosTernary.RepunitArchimedean

namespace ErdosTernary.RepunitDiophantine

open Narkiewicz
open ErdosTernary.RepunitBase4
open ErdosTernary.RepunitArchimedean

/-- A non-trivial joint survivor: an exponent s ≥ 5 that simultaneously:
    1. Survives the 3-adic tree to depth s: ∀ j < s, digit₃ (R_s(4)) j ≠ 2;
    2. Has its Archimedean quotient in the Cantor set: ⌊R_s(4) / 3^s⌋ ∈ Cantor. -/
def isJointSurvivor (s : ℕ) : Prop :=
  5 ≤ s ∧ (∀ j < s, digit₃ (repunit4 s) j ≠ 2) ∧ memCantorNat (repunit4 s / 3 ^ s)

/-- The set of all non-trivial joint survivors. -/
def jointSurvivors : Set ℕ :=
  {s : ℕ | isJointSurvivor s}

/-- The set of all exponents s whose power 4^s omits ternary digit 2. -/
def erdosSolutions : Set ℕ :=
  {s : ℕ | memCantorNat (4 ^ s)}

/-- Equivalence between joint survivors and non-trivial solutions:
    s is a joint survivor if and only if s ≥ 5 and 4^s belongs to the Cantor set. -/
theorem jointSurvivor_iff_pow4_memCantor_ge5 (s : ℕ) :
    isJointSurvivor s ↔ 5 ≤ s ∧ memCantorNat (4 ^ s) := by
  dsimp [isJointSurvivor]
  rw [memCantorNat_pow4_iff_adic_and_archimedean]

/-- The complete set of Erdős solutions decomposes exactly as the three
    classical solutions {0, 1, 4} union the set of non-trivial joint survivors. -/
theorem erdosSolutions_eq_base_union_joint :
    erdosSolutions = {0, 1, 4} ∪ jointSurvivors := by
  ext s
  simp only [erdosSolutions, jointSurvivors, isJointSurvivor, Set.mem_setOf_eq,
             Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [erdos_ternary_reduction]

/-- The Erdős Ternary Conjecture is logically equivalent to the emptiness
    of the non-trivial joint survivor set:
    erdosSolutions = {0, 1, 4} ↔ jointSurvivors = ∅. -/
theorem erdos_conjecture_iff_jointSurvivors_empty :
    erdosSolutions = {0, 1, 4} ↔ jointSurvivors = ∅ := by
  rw [erdosSolutions_eq_base_union_joint]
  constructor
  · intro h
    ext s
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hs
    have hs_sol : s ∈ {0, 1, 4} ∪ jointSurvivors := Set.mem_union_right _ hs
    rw [h] at hs_sol
    rcases hs_sol with rfl | rfl | rfl
    · have : 5 ≤ 0 := hs.1; omega
    · have : 5 ≤ 1 := hs.1; omega
    · have : 5 ≤ 4 := hs.1; omega
  · intro h
    rw [h, Set.union_empty]

/-- Finiteness reduction: If the joint survivor set is finite,
    then the full set of powers of two avoiding digit 2 is finite. -/
theorem finite_powers_of_two_of_finite_joint (h : jointSurvivors.Finite) :
    erdosSolutions.Finite := by
  rw [erdosSolutions_eq_base_union_joint]
  have hbase : ({0, 1, 4} : Set ℕ).Finite := by
    exact Set.toFinite {0, 1, 4}
  exact hbase.union h

end ErdosTernary.RepunitDiophantine
