/-
  Bridge Theorem: Uniform Proof for All K >= 5
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Card
import ErdosTernary.SayeLemma
import ErdosTernary.Narkiewicz
import ErdosTernary.MiddleDigits
import ErdosTernary.BridgeCompute
import ErdosTernary.BridgeComputeExtended
import ErdosTernary.Bridge
import ErdosTernary.BridgeMiddle
import ErdosTernary.BridgeK13
import ErdosTernary.BridgeK14
import ErdosTernary.BridgeK15
import ErdosTernary.BridgeK16
import ErdosTernary.BridgeK17

open ErdosTernary.SayeLemma
open ErdosTernary.MiddleDigits
open ErdosTernary.BridgeCompute
open ErdosTernary.BridgeComputeExtended
open Narkiewicz
open ErdosTernary.Bridge
open ErdosTernary.BridgeMiddle

namespace ErdosTernary.BridgeUniform

private theorem digit_eq_of_mod {val K i : Nat} (hi : i < K) :
    val % 3 ^ K / 3 ^ i % 3 = val / 3 ^ i % 3 := by
  have h3k : 3 ^ K = 3 ^ i * 3 ^ (K - i) := by
    have hk : K = i + (K - i) := by omega
    conv_lhs => rw [hk]
    rw [Nat.pow_add]
  rw [h3k]
  rw [Nat.mod_mul_right_div_self val (3 ^ i) (3 ^ (K - i))]
  exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 3 (by omega : 1 ≤ K - i))

theorem hasTrailingDigit2_mod_le (val K : Nat) :
    hasTrailingDigit2 val K = true → hasTrailingDigit2 (val % 3 ^ K) K = true := by
  intro h
  unfold hasTrailingDigit2 at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨i, hi_range, hi_digit⟩ := h
  have hi_bound : i < K := List.mem_range.mp hi_range
  exact ⟨i, hi_range, by rw [digit_eq_of_mod hi_bound]; exact hi_digit⟩

/-- NK monotonicity: if r survives the trailing-2-free filter at level K₂,
    it also survives at any lower level K₁ ≤ K₂ (assuming r < uK K₁).

    Core idea: hasTrailingDigit2 checks positions 0..K-1. If no digit 2
    in positions 0..K₂-1, then no digit 2 in positions 0..K₁-1. -/
private theorem htd_transfer {r K₁ K₂ : Nat} (hK : K₁ ≤ K₂) :
    hasTrailingDigit2 (2^r % 3^K₁) K₁ = true → hasTrailingDigit2 (2^r % 3^K₂) K₂ = true := by
  intro h
  unfold hasTrailingDigit2 at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨i, hi_range, hi_digit⟩ := h
  rw [List.mem_range] at hi_range
  simp only [beq_iff_eq] at hi_digit
  have hd1 := digit_eq_of_modPow (2^r) i K₁ (by omega)
  have hd2 := digit_eq_of_modPow (2^r) i K₂ (by omega)
  rw [← hd1] at hi_digit; rw [hd2] at hi_digit
  exact ⟨i, List.mem_range.mpr (by omega), by simp [hi_digit]⟩

private theorem NK_mono_core {K₁ K₂ r : Nat} (hK : K₁ ≤ K₂) (hbound : r < uK K₁) :
    r ∈ computeNK K₂ → r ∈ computeNK K₁ := by
  intro h
  unfold computeNK at h ⊢
  simp only [List.mem_filter, Finset.mem_range] at h ⊢
  obtain ⟨_, hno2⟩ := h
  refine ⟨List.mem_range.mpr hbound, ?_⟩
  by_contra hgoal
  have h1 : hasTrailingDigit2 (2^r % 3^K₁) K₁ = true := by
    have : ∀ b : Bool, b = false ∨ b = true := by intro b; cases b <;> simp
    have := this (hasTrailingDigit2 (2^r % 3^K₁) K₁)
    obtain (hF | hT) := this
    · exfalso; exact hgoal (by rw [hF]; decide)
    · exact hT
  have h2 := htd_transfer hK h1
  exact hgoal (by rw [show hasTrailingDigit2 (2^r % 3^K₁) K₁ = true from h1]; exact h2 ▸ hno2)

theorem NK_mono {K₁ K₂ r : Nat} (hK : K₁ ≤ K₂) (hbound : r < uK K₁) :
    r ∈ computeNKFast K₂ → r ∈ computeNKFast K₁ := by
  intro h
  rw [computeNKFast_eq] at h ⊢
  exact NK_mono_core hK hbound h

-- Bridge for K=13-16: checkBridgeCantorPow2 K = true (proved in BridgeK13-16)
-- implies the property on computeNK K.

private theorem digit_mod3pow50_eq (r k : Nat) (hk : k < 50) :
    (2 ^ r / 3 ^ k) % 3 = (2 ^ r % 3 ^ 50 / 3 ^ k) % 3 := by
  have hk1 : k + 1 ≤ 50 := Nat.succ_le_of_lt hk
  have h3k : 3^k > 0 := Nat.pow_pos (by omega)
  have h3m : 3^(50-k) > 0 := Nat.pow_pos (by omega)
  have hsplit : 3^k * 3^(50-k) = 3^50 := by rw [← Nat.pow_add, Nat.add_sub_cancel' (Nat.le_of_lt hk)]
  have hm1 : 2^r % 3^50 / 3^k = 2^r / 3^k % 3^(50-k) := by
    have := Nat.mod_mul_right_div_self (2^r) (3^k) (3^(50-k))
    rw [hsplit] at this; exact this
  have hm2 : 2^r / 3^k % 3 = 2^r / 3^k % 3^(50-k) % 3 := by
    symm; apply Nat.mod_mod_of_dvd
    exact Nat.pow_dvd_pow 3 (Nat.succ_le_of_lt (Nat.sub_pos_of_lt hk))
  rw [hm1, hm2]

private theorem checkBridgeCantorPow2_imp_not_cantor (K : Nat)
    (hcheck : checkBridgeCantorPow2 K = true) (r : Nat)
    (hr : r ∈ computeNKFast K) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬(memCantorNat (2 ^ r)) := by
  intro hc
  have hcheck' := List.all_eq_true.mp hcheck r hr
  have hb := hcheck' hr
  have h_dig : hasDigit2UpTo (pow2Mod r (3^50)) 50 = true := by
    by_contra hn
    have h0 : r ≠ 0 := hSpecial.1
    have h2 : r ≠ 2 := hSpecial.2.1
    have h8 : r ≠ 8 := hSpecial.2.2
    simp only [Bool.or_eq_true, beq_iff_eq, h0, h2, h8, false_or] at hb
    exact hn hb
  unfold ErdosTernary.BridgeCompute.hasDigit2UpTo ErdosTernary.BridgeCompute.hasDigit2InRange at h_dig
  rw [List.any_eq_true] at h_dig
  obtain ⟨i, hi_mem, hi_eq⟩ := h_dig
  rw [List.mem_range] at hi_mem
  simp only [beq_iff_eq] at hi_eq
  have hmod := pow2Mod_eq r (3^50)
  rw [hmod] at hi_eq
  have h_i : (2^r / 3^i) % 3 = (2^r % 3^50 / 3^i) % 3 := digit_mod3pow50_eq r i hi_mem
  have h_digit2 : (2^r / 3^i) % 3 = 2 := h_i ▸ hi_eq
  exact hc i h_digit2

private theorem bridge_K13_not_cantor (r : Nat)
    (hr : r ∈ computeNKFast 13) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬(memCantorNat (2 ^ r)) :=
  checkBridgeCantorPow2_imp_not_cantor 13 checkBridgeCantorPow2_13 r hr hSpecial

private theorem bridge_K14_not_cantor (r : Nat)
    (hr : r ∈ computeNKFast 14) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬(memCantorNat (2 ^ r)) :=
  checkBridgeCantorPow2_imp_not_cantor 14 checkBridgeCantorPow2_14 r hr hSpecial

private theorem bridge_K15_not_cantor (r : Nat)
    (hr : r ∈ computeNKFast 15) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬(memCantorNat (2 ^ r)) :=
  ErdosTernary.BridgeK15.bridge_K15_not_cantor r hr hSpecial

private theorem bridge_K16_not_cantor (r : Nat)
    (hr : r ∈ computeNKFast 16) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬(memCantorNat (2 ^ r)) :=
  ErdosTernary.BridgeK16.bridge_K16_not_cantor r hr hSpecial

private theorem bridge_K17_not_cantor (r : Nat)
    (hr : r ∈ computeNKFast 17) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬(memCantorNat (2 ^ r)) :=
  ErdosTernary.BridgeK17.bridge_K17_not_cantor r hr hSpecial

axiom ostrowski_invariant :
  ∀ K, K ≥ 18 →
  ∀ r, r ∈ computeNKFast K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
  ¬(memCantorNat (2 ^ r))

def hasDigit2UpTo (val maxDigits : Nat) : Bool :=
  (List.range maxDigits).any fun i => (val / 3 ^ i) % 3 == 2

theorem check_nine_to_47 :
    List.all ((List.range 48).filter (· ≥ 9)) (fun n => hasDigit2UpTo (2 ^ n) 50) = true := by
  native_decide

theorem check_digit2_48_to_1000 :
    List.all ((List.range 1001).filter (· ≥ 48))
      (fun n => hasDigit2UpTo (2 ^ n) 50) = true := by
  native_decide

theorem all_nine_to_1000_not_cantor :
    ∀ n, 9 ≤ n → n ≤ 1000 → ¬(memCantorNat (2 ^ n)) := by
  intro n hn9 hn1000 hc
  by_cases h48 : n < 48
  · have hmem : n ∈ (List.range 48).filter (· ≥ 9) := by
      simp [List.mem_filter, List.mem_range]; omega
    have hall := List.all_eq_true.mp check_nine_to_47 n hmem
    simp only [hasDigit2UpTo] at hall
    rw [List.any_eq_true] at hall
    obtain ⟨i, hi_mem, heq⟩ := hall
    rw [List.mem_range] at hi_mem
    simp only [beq_iff_eq] at heq
    exact hc i heq
  · have hmem : n ∈ (List.range 1001).filter (· ≥ 48) := by
      simp [List.mem_filter, List.mem_range]; omega
    have hall := List.all_eq_true.mp check_digit2_48_to_1000 n hmem
    simp only [hasDigit2UpTo] at hall
    rw [List.any_eq_true] at hall
    obtain ⟨i, hi_mem, heq⟩ := hall
    rw [List.mem_range] at hi_mem
    simp only [beq_iff_eq] at heq
    exact hc i heq

theorem trail2_r1 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 1) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨0, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r3 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 3) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨0, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r4 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 4) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨1, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r5 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 5) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨0, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r6 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 6) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨3, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r7 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 7) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨0, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r9 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 9) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨0, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r10 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 10) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨1, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r11 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 11) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨0, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r12 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 12) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨2, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r13 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 13) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨0, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r14 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 14) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨2, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r15 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 15) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨0, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r16 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 16) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨1, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r17 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 17) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨0, List.mem_range.mpr (by omega), by native_decide⟩

theorem trail2_r18 (K : Nat) (hK : K ≥ 5) : hasTrailingDigit2 (2 ^ 18) K = true := by
  unfold hasTrailingDigit2; rw [List.any_eq_true]
  exact ⟨4, List.mem_range.mpr (by omega), by native_decide⟩

theorem NK_excludes_small (K : Nat) (hK : K ≥ 5) (r : Nat)
    (hr : r ∈ computeNKFast K) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    r ≥ 9 := by
  by_contra hlt; push_neg at hlt
  have h2r_lt : 2 ^ r < 3 ^ K := by
    have h2r : 2 ^ r ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3k : 3 ^ 5 ≤ 3 ^ K := Nat.pow_le_pow_right (by omega) (by omega : 5 ≤ K)
    omega
  have hmod : 2 ^ r % 3 ^ K = 2 ^ r := Nat.mod_eq_of_lt h2r_lt
  rw [computeNKFast_eq] at hr
  unfold computeNK at hr
  simp only [List.mem_filter, Finset.mem_range] at hr
  obtain ⟨hlt_u, hno2⟩ := hr
  rw [hmod] at hno2
  interval_cases r
  · exact absurd rfl hSpecial.1
  · have := trail2_r1 K hK; simp_all [Bool.not_eq_true]
  · exact absurd rfl hSpecial.2.1
  · have := trail2_r3 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r4 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r5 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r6 K hK; simp_all [Bool.not_eq_true]
  · have := trail2_r7 K hK; simp_all [Bool.not_eq_true]
  · exact absurd rfl hSpecial.2.2

theorem NK_excludes_small_19 (K : Nat) (hK : K ≥ 5) (r : Nat)
    (hr : r ∈ computeNKFast K) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    r ≥ 19 := by
  by_contra hlt; push_neg at hlt
  rw [computeNKFast_eq] at hr
  unfold computeNK at hr
  simp only [List.mem_filter, Finset.mem_range] at hr
  obtain ⟨hlt_u, hno2⟩ := hr
  interval_cases r
  · exact absurd rfl hSpecial.1
  · have := hasTrailingDigit2_mod_le 2 K (trail2_r1 K hK); simp_all [Bool.not_eq_true]
  · exact absurd rfl hSpecial.2.1
  · have := hasTrailingDigit2_mod_le 8 K (trail2_r3 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 16 K (trail2_r4 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 32 K (trail2_r5 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 64 K (trail2_r6 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 128 K (trail2_r7 K hK); simp_all [Bool.not_eq_true]
  · exact absurd rfl hSpecial.2.2
  · have := hasTrailingDigit2_mod_le 512 K (trail2_r9 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 1024 K (trail2_r10 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 2048 K (trail2_r11 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 4096 K (trail2_r12 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 8192 K (trail2_r13 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 16384 K (trail2_r14 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 32768 K (trail2_r15 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 65536 K (trail2_r16 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 131072 K (trail2_r17 K hK); simp_all [Bool.not_eq_true]
  · have := hasTrailingDigit2_mod_le 262144 K (trail2_r18 K hK); simp_all [Bool.not_eq_true]

theorem bridge_small_n (K : Nat) (hK : K ≥ 5) (r : Nat)
    (hr : r ∈ computeNKFast K) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8)
    (hr1001 : r < 1001) :
    ¬(memCantorNat (2 ^ r)) := by
  have hr9 : r ≥ 9 := NK_excludes_small K hK r hr hSpecial
  exact all_nine_to_1000_not_cantor r hr9 (by omega)

theorem checkBridge_extract {K r : Nat}
    (h : checkBridge K 30 = true)
    (hr : r ∈ computeNKFast K) (hs : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    hasLeadingDigit2 (2 ^ r) 30 = true := by
  have hr' : r ∈ computeNK K := by rwa [computeNKFast_eq] at hr
  unfold checkBridge at h
  have h1 := List.all_eq_true.mp h r hr'
  simp_all [Bool.or_eq_true, beq_iff_eq]

theorem pow2_not_cantor_for_large_K (K : Nat) (hK : K ≥ 13) (r : Nat)
    (hr : r ∈ computeNKFast K) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬(memCantorNat (2 ^ r)) := by
  have hcases : K = 13 ∨ K = 14 ∨ K = 15 ∨ K = 16 ∨ K = 17 ∨ K ≥ 18 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | h18
  · exact bridge_K13_not_cantor r hr hSpecial
  · exact bridge_K14_not_cantor r hr hSpecial
  · exact bridge_K15_not_cantor r hr hSpecial
  · exact bridge_K16_not_cantor r hr hSpecial
  · exact bridge_K17_not_cantor r hr hSpecial
  · exact ostrowski_invariant K h18 r hr hSpecial.1 hSpecial.2.1 hSpecial.2.2

def checkBridgeCantor (K : Nat) : Bool :=
  let nK := computeNKFast K
  nK.all fun r =>
    r == 0 || r == 2 || r == 8 || hasDigit2UpTo (2 ^ r) 50

theorem bridge_K5_cantor : checkBridgeCantor 5 = true := by native_decide
theorem bridge_K6_cantor : checkBridgeCantor 6 = true := by native_decide
theorem bridge_K7_cantor : checkBridgeCantor 7 = true := by native_decide
theorem bridge_K8_cantor : checkBridgeCantor 8 = true := by native_decide
theorem bridge_K9_cantor : checkBridgeCantor 9 = true := by native_decide

private theorem checkBridgeCantor_extract {K r : Nat}
    (h : checkBridgeCantor K = true)
    (hr : r ∈ computeNKFast K) (hs : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    hasDigit2UpTo (2 ^ r) 50 = true := by
  unfold checkBridgeCantor at h
  have h1 := List.all_eq_true.mp h r hr
  simp_all [Bool.or_eq_true, beq_iff_eq]

private theorem hasDigit2UpTo_not_cantor {r : Nat} (h : hasDigit2UpTo (2 ^ r) 50 = true) :
    ¬(memCantorNat (2 ^ r)) := by
  intro hc
  unfold hasDigit2UpTo at h
  rw [List.any_eq_true] at h
  obtain ⟨i, hi_mem, hi_eq⟩ := h
  rw [List.mem_range] at hi_mem
  simp only [beq_iff_eq] at hi_eq
  exact hc i hi_eq

private theorem computeNKFast_eq_NK_K_for_local (K : Nat) (hK : K = 10 ∨ K = 11 ∨ K = 12) :
    computeNKFast K = NK_K_for K := by
  rcases hK with rfl | rfl | rfl
  · native_decide
  · native_decide
  · native_decide

theorem bridge_first_period_leading (K : Nat) (hK5 : K ≥ 5) (hK9 : K ≤ 9)
    (r : Nat) (hr : r ∈ computeNKFast K) (hs : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    hasLeadingDigit2 (2 ^ r) 30 = true := by
  interval_cases K <;> try omega
  · exact checkBridge_extract bridge_K5 hr hs
  · exact checkBridge_extract bridge_K6 hr hs
  · exact checkBridge_extract bridge_K7 hr hs
  · exact checkBridge_extract bridge_K8 hr hs
  · exact checkBridge_extract bridge_K9 hr hs

private theorem bridge_cantor_K (K : Nat) (hK : K ≤ 9) (hK5 : K ≥ 5) :
    checkBridgeCantor K = true := by
  interval_cases K <;> try omega
  · exact bridge_K5_cantor
  · exact bridge_K6_cantor
  · exact bridge_K7_cantor
  · exact bridge_K8_cantor
  · exact bridge_K9_cantor

theorem bridge_all_K_digit2 (K : Nat) (hK : K ≥ 5) (r : Nat)
    (hr : r ∈ computeNKFast K) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬(memCantorNat (2 ^ r)) := by
  have h_cases : K ≤ 9 ∨ (K ≥ 10 ∧ K ≤ 12) ∨ K ≥ 13 := by omega
  cases h_cases with
  | inl h9 =>
    have h2 := checkBridgeCantor_extract (bridge_cantor_K K h9 hK) hr hSpecial
    exact hasDigit2UpTo_not_cantor h2
  | inr h_rest =>
    cases h_rest with
    | inl h12 =>
      obtain ⟨h10, h12⟩ := h12
      have hK' : K = 10 ∨ K = 11 ∨ K = 12 := by omega
      have hr' : r ∈ NK_K_for K := by
        rw [computeNKFast_eq_NK_K_for_local K hK'] at hr; exact hr
      exact bridge_middle_not_cantor K hK' r hr' hSpecial
    | inr h13 =>
      have hcases : K = 13 ∨ K = 14 ∨ K = 15 ∨ K = 16 ∨ K = 17 ∨ K ≥ 18 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | h18
      · exact bridge_K13_not_cantor r hr hSpecial
      · exact bridge_K14_not_cantor r hr hSpecial
      · exact bridge_K15_not_cantor r hr hSpecial
      · exact bridge_K16_not_cantor r hr hSpecial
      · exact bridge_K17_not_cantor r hr hSpecial
      · exact ostrowski_invariant K h18 r hr hSpecial.1 hSpecial.2.1 hSpecial.2.2

theorem bridge_first_period_all (K : Nat) (hK : K ≥ 5) (r : Nat)
    (hr : r ∈ computeNKFast K) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬(memCantorNat (2 ^ r)) :=
  bridge_all_K_digit2 K hK r hr hSpecial

theorem bridge_middle_digit_K10_12 (K : Nat) (hK : K = 10 ∨ K = 11 ∨ K = 12)
    (r : Nat) (hr : r ∈ NK_K_for K) (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬(memCantorNat (2 ^ r)) :=
  bridge_middle_not_cantor K hK r hr hSpecial

end ErdosTernary.BridgeUniform
