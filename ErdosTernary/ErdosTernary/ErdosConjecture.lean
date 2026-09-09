import Mathlib.Tactic
import ErdosTernary.SignFlip
import ErdosTernary.BridgeCompute
import ErdosTernary.BridgeUniform
import ErdosTernary.Narkiewicz

open ErdosTernary.BridgeCompute
open ErdosTernary.BridgeUniform
open Narkiewicz

namespace ErdosTernary

private theorem pow3_ge_succ (n : Nat) : 3 ^ n ≥ n + 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc 3 ^ (n + 1) = 3 * 3 ^ n := by ring
      _ ≥ 3 * (n + 1) := Nat.mul_le_mul_left 3 ih
      _ ≥ n + 2 := by omega

private theorem bnot_eq_true {b : Bool} : (!b) = true ↔ b = false := by
  cases b <;> simp

private theorem exists_K_ge5 (r : Nat) : ∃ K ≥ 5, r < uK K := by
  refine ⟨r + 5, by omega, ?_⟩
  unfold uK
  show r < 2 * 3 ^ (r + 5 - 1)
  simp only [show r + 5 - 1 = r + 4 from by omega]
  linarith [Nat.mul_le_mul_left 2 (pow3_ge_succ (r + 4))]

theorem erdos_ternary :
    ∀ r, r ≠ 0 → r ≠ 2 → r ≠ 8 → ¬memCantorNat (2 ^ r) := by
  intro r h0 h2 h8 hc
  obtain ⟨K, hK5, hrK⟩ := exists_K_ge5 r
  have hrNK : r ∈ computeNK K := by
    unfold computeNK
    simp only [List.mem_filter, Finset.mem_range]
    refine ⟨List.mem_range.mpr hrK, ?_⟩
    unfold hasTrailingDigit2
    rw [bnot_eq_true, ← Bool.not_eq_true]
    intro h
    rw [List.any_eq_true] at h
    obtain ⟨i, hi, heq⟩ := h
    rw [List.mem_range] at hi
    simp only [beq_iff_eq] at heq
    have h_eq := digit_eq_of_modPow (2 ^ r) i K (by omega)
    have : digit₃ (2 ^ r) i = 2 := by unfold digit₃; linarith
    exact absurd this (hc i)
  have hspec : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8 := ⟨h0, h2, h8⟩
  exact bridge_first_period_all K hK5 r hrNK hspec hc

end ErdosTernary

#check @ErdosTernary.erdos_ternary
#print axioms ErdosTernary.erdos_ternary
#print ErdosTernary.erdos_ternary
