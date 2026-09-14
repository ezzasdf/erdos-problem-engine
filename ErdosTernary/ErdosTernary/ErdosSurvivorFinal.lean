/-
  ErdosSurvivorFinal.lean — The Erdős Ternary Conjecture: Clean Final Statement

  No sorry. No new axioms beyond propext, Classical.choice, Lean.ofReduceBool, Quot.sound.
-/

import ErdosTernary.ExponentBound

open ErdosTernary.BridgeCompute
open Narkiewicz
open ErdosTernary.Lifting
open ErdosTernary.CarryAnalysis
open ErdosTernary.ThreeLevelCompat

/-- The Erdős survivor classification. -/
theorem erdos_survivor_classification (r : Nat)
    (h_survive : ∀ K, r ∈ computeNK K) :
    r = 0 ∨ r = 2 ∨ r = 8 :=
  erdos_survivor_conjecture r h_survive

/-- Survivor implies Cantor. -/
theorem survivor_implies_cantor (r : Nat)
    (h_survive : ∀ K, r ∈ computeNK K) :
    memCantorNat (2 ^ r) :=
  eventually_survivor_is_cantor r h_survive

/-- Combined. -/
theorem survivor_cantor_nonexception (r : Nat)
    (h_survive : ∀ K, r ∈ computeNK K)
    (h0 : r ≠ 0) (h2 : r ≠ 2) (h8 : r ≠ 8) :
    memCantorNat (2 ^ r) ∧ r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8 :=
  survivor_reduction r h_survive h0 h2 h8

/-- Digit-form implies survivor. -/
theorem erdos_conjecture_digit_to_survivor :
    (∀ r, r ≠ 0 → r ≠ 2 → r ≠ 8 → ∃ i, digit₃ (2 ^ r) i = 2) →
    (∀ r, memCantorNat (2 ^ r) → r = 0 ∨ r = 2 ∨ r = 8) := by
  intro h r hc
  by_contra hne; push_neg at hne
  obtain ⟨h0, h2, h8⟩ := hne
  obtain ⟨i, hi⟩ := h r h0 h2 h8; exact hc i hi

/-! ## The Eventual Survivor Lemma

If 2^r is Cantor (no digit 2), then r % uK K ∈ computeNK K for all K ≥ 1.
Key: Euler's theorem gives 2^r ≡ 2^(r%uK K) (mod 3^K) via pow2_add_uK_mod.
-/

private lemma uK_pos (K : Nat) : 0 < uK K := by
  unfold uK; exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))

/-- The eventual survivor lemma. -/
theorem memCantorNat_2pow_mem_NK (r K : Nat) (hK : K ≥ 1)
    (hc : memCantorNat (2 ^ r)) :
    r % uK K ∈ computeNK K := by
  have hlt : r % uK K < uK K := Nat.mod_lt _ (uK_pos K)
  have heuler := pow2_add_uK_mod K (r % uK K) (r / uK K) hK
  have hr_eq : r % uK K + (r / uK K) * uK K = r := by
    rw [Nat.mul_comm]; exact Nat.mod_add_div r (uK K)
  rw [hr_eq] at heuler
  unfold computeNK
  simp only [List.mem_filter, List.mem_range]
  constructor
  · exact hlt
  · suffices h_no2 : hasTrailingDigit2 (2 ^ (r % uK K) % 3 ^ K) K = false by simp [h_no2]
    unfold hasTrailingDigit2
    rw [← Bool.not_eq_true]
    intro h
    rw [List.any_eq_true] at h
    obtain ⟨i, hi_mem, hi_eq⟩ := h
    rw [List.mem_range] at hi_mem
    simp only [beq_iff_eq] at hi_eq
    have h_digit := digit_eq_of_modPow (2 ^ r) i K hi_mem
    rw [heuler] at h_digit
    rw [← h_digit] at hi_eq
    exact hc i hi_eq

/-- If 2^r is Cantor, then r ∈ computeNK K for all K > r+1. -/
theorem memCantorNat_2pow_eventual (r : Nat)
    (hc : memCantorNat (2 ^ r)) :
    ∃ K₀, ∀ K > K₀, r ∈ computeNK K := by
  refine ⟨r + 1, fun K hK => ?_⟩
  have hKge : K ≥ r + 2 := by omega
  have hmem := memCantorNat_2pow_mem_NK r K (by omega) hc
  have hr_eq : r % uK K = r := by
    apply Nat.mod_eq_of_lt; exact uK_gt_of_large r K hKge
  rw [hr_eq] at hmem; exact hmem

/-! ## Inlined Bridge Contradiction -/

private theorem digit2_from_hasDigit2UpTo {r i : Nat}
    (hi : i < 50)
    (hmod : (2 ^ r % 3 ^ 50 / 3 ^ i) % 3 = 2) :
    (2 ^ r / 3 ^ i) % 3 = 2 := by
  have h := digit_eq_of_modPow (2 ^ r) i 50 hi; omega

private theorem cantor_bridge_contradicts_local (K r : Nat)
    (hcheck : checkBridgeCantorPow2 K = true)
    (hr : r ∈ computeNKFast K)
    (h0 : r ≠ 0) (h2 : r ≠ 2) (h8 : r ≠ 8) :
    ∃ i < 50, (2 ^ r / 3 ^ i) % 3 = 2 := by
  unfold checkBridgeCantorPow2 at hcheck
  have hall := List.all_eq_true.mp hcheck r hr
  have h0f : (r == 0) = false := by cases h : r == 0 <;> simp_all [beq_iff_eq]
  have h2f : (r == 2) = false := by cases h : r == 2 <;> simp_all [beq_iff_eq]
  have h8f : (r == 8) = false := by cases h : r == 8 <;> simp_all [beq_iff_eq]
  simp only [h0f, h2f, h8f, Bool.false_or] at hall
  unfold ErdosTernary.BridgeCompute.hasDigit2UpTo ErdosTernary.BridgeCompute.hasDigit2InRange at hall
  rw [List.any_eq_true] at hall
  obtain ⟨i, hi_mem, hi_eq⟩ := hall
  rw [List.mem_range] at hi_mem
  simp only [beq_iff_eq, Nat.zero_add] at hi_eq
  rw [pow2Mod_eq r (3^50)] at hi_eq
  exact ⟨i, hi_mem, digit2_from_hasDigit2UpTo hi_mem hi_eq⟩

/-! ## The Digit-Form Conjecture for Small r -/

/-- For r < uK 13, the Cantor property forces r ∈ {0,2,8}. -/
theorem erdos_digit2_conjecture_small (r : Nat) (hr : r < uK 13)
    (hc : memCantorNat (2 ^ r)) :
    r = 0 ∨ r = 2 ∨ r = 8 := by
  have h13 := memCantorNat_2pow_mem_NK r 13 (by omega) hc
  rw [Nat.mod_eq_of_lt hr] at h13
  have h13fast : r ∈ computeNKFast 13 := by rw [computeNKFast_eq]; exact h13
  by_contra hne; push_neg at hne
  obtain ⟨h0, h2, h8⟩ := hne
  obtain ⟨i, _, hdigit2⟩ :=
    cantor_bridge_contradicts_local 13 r checkBridgeCantorPow2_13 h13fast h0 h2 h8
  exact hc i hdigit2

/-! ## The Erdős Digit-Form Conjecture (Full)

If 2^r has no digit 2 in its ternary expansion, then r ∈ {0, 2, 8}.

Proof sketch:
- For r < uK 13: use the small-r bridge (checkBridgeCantorPow2_13).
- For r ≥ uK 13: the eventual survivor lemma gives r ∈ N_K for all large K.
  Choosing K ≥ 13 with r ∈ N_K, the uniform bridge (pow2_not_cantor_for_large_K
  from BridgeUniform) shows ¬memCantorNat(2^r), contradiction.

Status: PROVED via erdos_digit2_conjecture_small for r < uK 13.
The r ≥ uK 13 case requires BridgeUniform (not yet compiled — see below).
-/

/-! ## Summary

  1. Survivor → Classify:   (∀ K, r ∈ N_K) → r ∈ {0, 2, 8}
  2. Survivor → Cantor:     (∀ K, r ∈ N_K) → memCantorNat(2^r)
  3. Eventual Survivor:     memCantorNat(2^r) → ∃ K₀, ∀ K > K₀, r ∈ N_K
  4. Small-r Conjecture:    memCantorNat(2^r) ∧ r < uK 13 → r ∈ {0,2,8}

Axioms: propext, Classical.choice, Lean.ofReduceBool, Quot.sound.

OPEN: Full digit-form conjecture for r ≥ uK 13.
Requires BridgeUniform.lean (contains pow2_not_cantor_for_large_K),
which in turn requires BridgeK14, BridgeK17, BridgeK18, BridgeCantorChunkedProofs.
-/
