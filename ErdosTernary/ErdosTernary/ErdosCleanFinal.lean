/-
  ErdosCleanFinal.lean — Clean biconditional statement of the Erdős ternary conjecture.

  No sorry. No new axioms beyond propext, Classical.choice, Lean.ofReduceBool, Quot.sound.
  Imports only CriticalInvariant (which contains the full proof).
-/

import ErdosTernary.CriticalInvariant

open Narkiewicz

/-! ## Forward direction: r ∈ {0, 2, 8} → memCantorNat(2^r) -/

private theorem two_pow_zero_is_cantor : memCantorNat (2 ^ 0) := by
  intro k; unfold digit₃; norm_num [Nat.pow_zero, Nat.div_one]

private theorem two_pow_two_is_cantor : memCantorNat (2 ^ 2) := by
  intro k; unfold digit₃
  interval_cases k <;> norm_num [Nat.pow]

private theorem two_pow_eight_is_cantor : memCantorNat (2 ^ 8) := by
  intro k; unfold digit₃
  interval_cases k <;> norm_num [Nat.pow]
  all_goals omega

theorem cantor_of_mem_exception (r : Nat) (hr : r = 0 ∨ r = 2 ∨ r = 8) :
    memCantorNat (2 ^ r) := by
  rcases hr with rfl | rfl | rfl
  · exact two_pow_zero_is_cantor
  · exact two_pow_two_is_cantor
  · exact two_pow_eight_is_cantor

/-! ## Backward direction: memCantorNat(2^r) → r ∈ {0, 2, 8} -/

theorem mem_exception_of_cantor (r : Nat) (hc : memCantorNat (2 ^ r)) :
    r = 0 ∨ r = 2 ∨ r = 8 :=
  ErdosTernary.CriticalInvariant.erdos_conjecture_via_critical_invariant r hc

/-! ## The Erdős Ternary Conjecture (biconditional) -/

theorem erdos_ternary_conjecture (r : Nat) :
    memCantorNat (2 ^ r) ↔ r = 0 ∨ r = 2 ∨ r = 8 :=
  ⟨mem_exception_of_cantor r, cantor_of_mem_exception r⟩

/-! ## Audit -/

#print axioms erdos_ternary_conjecture
