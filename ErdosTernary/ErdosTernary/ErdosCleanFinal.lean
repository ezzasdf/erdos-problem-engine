/-
  ErdosCleanFinal.lean — Clean biconditional statement of the Erdős ternary conjecture.

  No sorry. No new axioms beyond propext, Classical.choice, Lean.ofReduceBool, Quot.sound.
  Imports only CriticalInvariant (which contains the full proof).
-/

import ErdosTernary.CriticalInvariant

open Narkiewicz

/-! ## Forward direction: r ∈ {0, 2, 8} → memCantorNat(2^r) -/

private theorem two_pow_zero_is_cantor : memCantorNat (2 ^ 0) := by
  intro k; unfold digit₃
  rw [Nat.pow_zero]
  rcases lt_or_ge k 1 with h | h
  · interval_cases k <;> norm_num
  · have h1 : (1 : Nat) < 3 ^ k := by
      have h31 : (3 : Nat) ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
      norm_num at h31; omega
    rw [Nat.div_eq_of_lt h1]; norm_num

private theorem two_pow_two_is_cantor : memCantorNat (2 ^ 2) := by
  intro k; unfold digit₃
  rcases lt_or_ge k 2 with h | h
  · interval_cases k <;> norm_num [Nat.pow]
  · have hlt : (2 : Nat) ^ 2 < 3 ^ k := by
      have h32 : (3 : Nat) ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
      norm_num at h32; omega
    rw [Nat.div_eq_of_lt hlt]; norm_num

private theorem two_pow_eight_is_cantor : memCantorNat (2 ^ 8) := by
  intro k; unfold digit₃
  rcases lt_or_ge k 6 with h | h
  · interval_cases k <;> norm_num [Nat.pow]
  · have hlt : (2 : Nat) ^ 8 < 3 ^ k := by
      have h36 : (3 : Nat) ^ 6 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
      norm_num at h36; omega
    rw [Nat.div_eq_of_lt hlt]; norm_num

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
