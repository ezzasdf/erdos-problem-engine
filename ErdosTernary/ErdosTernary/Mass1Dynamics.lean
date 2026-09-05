/-
  Mass-1 Dynamics: Identifying Ostrowski mass-one residues in N_K.

  A residue r has Ostrowski mass 1 if r = q_j + ℓ with 5 ≤ j and ℓ ≤ 18,
  where q_j are convergent denominators of the partial quotients of log₃(2).
  This module filters N_K to extract exactly these mass-one elements.
-/

import Mathlib.Tactic
import ErdosTernary.OstrowskiFormLemma
import ErdosTernary.BridgeCompute

open ErdosTernary.SayeLemma
open ErdosTernary.BridgeCompute
open ErdosTernary.OstrowskiFormLemma
open Narkiewicz

namespace ErdosTernary.Mass1Dynamics

/-- A natural number r has Ostrowski mass one if it is of the form
    `Q Al32 j + ℓ` with `5 ≤ j` and `ℓ ≤ 18`. -/
def isMassOneForm (r : ℕ) : Prop :=
  ∃ j ℓ, 5 ≤ j ∧ ℓ ≤ 18 ∧ r = Q Al32 j + ℓ

/-- Boolean test: does `r` have the form `Q Al32 j + ℓ` with `5 ≤ j`, `ℓ ≤ 18`? -/
def isMassOneFormB (r : ℕ) : Bool :=
  (List.range 19).any fun ℓ =>
    (List.range (r + 19)).any fun j =>
      (5 ≤ j) && (ℓ ≤ 18) && (r == Q Al32 j + ℓ)

private lemma QAl32_ge_one (j : ℕ) : 1 ≤ Q Al32 j :=
  Q_pos (A := Al32) j

private lemma QAl32_ge (j : ℕ) : j ≤ Q Al32 j + 18 := by
  rcases j with _ | j
  · simp [Q]
  · have h := Q_ge_index Al32_hyp (j + 1) (by omega)
    omega

theorem isMassOneFormB_iff {r : ℕ} :
    isMassOneFormB r = true ↔ isMassOneForm r := by
  unfold isMassOneFormB isMassOneForm
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨ℓ, hℓ, hrest⟩ := h
    rw [List.mem_range] at hℓ
    rw [List.any_eq_true] at hrest
    obtain ⟨j, hj, hdec⟩ := hrest
    rw [List.mem_range] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
    have : r = Q Al32 j + ℓ := by
      have := hdec.2
      rwa [beq_iff_eq] at this
    exact ⟨j, ℓ, hdec.1.1, hdec.1.2, this⟩
  · intro ⟨j, ℓ, hj5, hℓ18, hr⟩
    have hj := QAl32_ge j
    rw [List.any_eq_true]
    refine ⟨ℓ, List.mem_range.mpr (by omega), ?_⟩
    rw [List.any_eq_true]
    refine ⟨j, List.mem_range.mpr (by omega), ?_⟩
    simp [hj5, hℓ18, hr]

instance : DecidablePred isMassOneForm := fun r =>
  decidable_of_iff (isMassOneFormB r = true) isMassOneFormB_iff

/-- Filter N_K to obtain residues with Ostrowski mass one. -/
def mass1_in_NK (K : ℕ) : List ℕ :=
  (computeNK K).filter fun r => decide (isMassOneForm r)

/-- If r has exactly one nonzero Ostrowski coefficient (value 1) at position j ≥ 5,
    then r has the mass-1 form. -/
theorem mass1_of_gd (r : ℕ) {j : ℕ} (hj : 5 ≤ j)
    (h1 : gd Al32 Al32_hyp j r = 1)
    (h0 : ∀ k, 5 ≤ k → k ≠ j → gd Al32 Al32_hyp k r = 0) :
    isMassOneForm r := by
  have := (mass_one_iff Al32_hyp Ql32_5 Ql32_hyp6 r).mp ⟨j, hj, h1, h0⟩
  exact this

/-- If r has the mass-1 form (r = Q Al32 j + ℓ with j ≥ 5, ℓ ≤ 18),
    then r has exactly one nonzero Ostrowski coefficient (value 1) at position j. -/
theorem gd_of_mass1 (r : ℕ) {j ℓ : ℕ} (hj : 5 ≤ j) (hℓ : ℓ ≤ 18)
    (hr : r = Q Al32 j + ℓ) :
    gd Al32 Al32_hyp j r = 1 ∧
    ∀ k, 5 ≤ k → k ≠ j → gd Al32 Al32_hyp k r = 0 := by
  have := coef_unique_of_form Al32_hyp Ql32_5 Ql32_hyp6 j ℓ hj hℓ
  subst hr
  exact this

/-- The mass-1 form characterization: r has exactly one nonzero Ostrowski
    coefficient at position ≥ 5 (value 1) if and only if r = Q Al32 j + ℓ
    for some j ≥ 5 and ℓ ≤ 18. -/
theorem mass1_form_eq (r : ℕ) :
    (∃ j, 5 ≤ j ∧ gd Al32 Al32_hyp j r = 1 ∧
      ∀ k, 5 ≤ k → k ≠ j → gd Al32 Al32_hyp k r = 0) ↔ isMassOneForm r :=
  ⟨fun ⟨j, hj, h1, h0⟩ => mass1_of_gd r hj h1 h0,
    fun ⟨j, ℓ, hj, hℓ, hr⟩ => ⟨j, hj, (gd_of_mass1 r hj hℓ hr).1,
      fun k hk hne => (gd_of_mass1 r hj hℓ hr).2 k hk hne⟩⟩

/-! ### Efficient bounded version for native_decide

    The naive `isMassOneFormB` creates `List.range (r + 19)` which for r up to
    2·3^11 ≈ 354K is prohibitively slow for `native_decide`. Since Q(j) grows
    exponentially with Q(15) = 16785921 > 531441 = 2·3^12, we only need to check
    j ≤ 14. We bound j at 20 for safety. -/

private def isMassOneFormB' (r : ℕ) : Bool :=
  (List.range 19).any fun ℓ =>
    (List.range 21).any fun j =>
      (5 ≤ j) && (ℓ ≤ 18) && (r == Q Al32 j + ℓ)

private lemma Q15_exceeds : 2 * 3 ^ 12 < Q Al32 15 := by native_decide

private lemma Q_increasing : ∀ j ≥ 1, Q Al32 j < Q Al32 (j + 1) :=
  Q_succ_gt Al32_hyp

private lemma Q_ge_15 (j : ℕ) (hj : 15 ≤ j) : Q Al32 15 ≤ Q Al32 j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 := Q_increasing (15 + n) (by omega)
    exact le_trans h1 (le_of_lt h2)

private lemma Q_no_mass1_above_15 (r : ℕ) (hr : r < 2 * 3 ^ 12) (j : ℕ) (hj : 15 ≤ j) (ℓ : ℕ) :
    r ≠ Q Al32 j + ℓ := by
  have := Q_ge_15 j hj
  have := Q15_exceeds
  linarith

private lemma isMassOneFormB'_iff {r : ℕ} (hr : r < 2 * 3 ^ 12) :
    (isMassOneFormB' r = true) ↔ isMassOneForm r := by
  unfold isMassOneFormB' isMassOneForm
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨ℓ, hℓ, hrest⟩ := h
    rw [List.mem_range] at hℓ
    rw [List.any_eq_true] at hrest
    obtain ⟨j, hj, hdec⟩ := hrest
    rw [List.mem_range] at hj
    simp only [Bool.and_eq_true] at hdec
    obtain ⟨⟨hj5, hℓ18⟩, heq⟩ := hdec
    rw [decide_eq_true_eq] at hj5 hℓ18
    have hr : r = Q Al32 j + ℓ := by rwa [beq_iff_eq] at heq
    exact ⟨j, ℓ, hj5, hℓ18, hr⟩
  · intro ⟨j, ℓ, hj5, hℓ18, hr_eq⟩
    have hj20 : j ≤ 20 := by
      by_contra hj'
      push_neg at hj'
      have : 15 ≤ j := by omega
      exact absurd hr_eq (Q_no_mass1_above_15 r hr j this ℓ)
    rw [List.any_eq_true]
    refine ⟨ℓ, List.mem_range.mpr (by omega), ?_⟩
    rw [List.any_eq_true]
    refine ⟨j, List.mem_range.mpr (by omega), ?_⟩
    simp [hj5, hℓ18, hr_eq]

private lemma computeNK_lt_uK (K : ℕ) (r : ℕ) (hr : r ∈ computeNK K) : r < uK K := by
  unfold computeNK at hr
  rw [List.mem_filter] at hr
  exact List.mem_range.mp hr.left

private lemma uK_12_lt : uK 12 < 2 * 3 ^ 12 := by
  unfold uK
  norm_num

private lemma bool_eq_of_iff_true {a b : Bool} (h : (a = true) ↔ (b = true)) : a = b := by
  cases a <;> cases b <;> simp at h <;> simp

private lemma filter_pred_eq {r : ℕ} (hr : r ∈ computeNK 12) :
    (decide (isMassOneForm r) : Bool) = isMassOneFormB' r := by
  have hr_lt : r < 2 * 3 ^ 12 :=
    lt_trans (computeNK_lt_uK 12 r hr) uK_12_lt
  apply bool_eq_of_iff_true
  constructor
  · intro h
    have : isMassOneForm r := decide_eq_true_eq.mp h
    exact (isMassOneFormB'_iff hr_lt).mpr this
  · intro h
    have : isMassOneForm r := (isMassOneFormB'_iff hr_lt).mp h
    exact decide_eq_true_eq.mpr this

/-- Base case: no element of N_12 has mass-1 form. Verified by native_decide
    over all 2048 residues in N_12, using a bounded j range (j ≤ 20) since
    Q(15) = 16785921 > 531441 = 2·3^12. -/
theorem mass1_in_NK_empty_K12 : mass1_in_NK 12 = [] := by
  unfold mass1_in_NK
  rw [List.filter_congr (fun r hr => filter_pred_eq hr)]
  native_decide

/-- Helper: for K ≤ 12, Q(15) > uK(K), so isMassOneFormB' suffices. -/
private lemma uK_le_pow12 (K : ℕ) (hK : K ≤ 12) : uK K < 2 * 3 ^ 12 := by
  unfold uK
  have : K - 1 ≤ 11 := by omega
  have : 3 ^ (K - 1) ≤ 3 ^ 11 :=
    Nat.pow_le_pow_right (by norm_num : 0 < 3) this
  linarith

private lemma filter_pred_eq_gen {K : ℕ} (hK : K ≤ 12)
    {r : ℕ} (hr : r ∈ computeNK K) :
    (decide (isMassOneForm r) : Bool) = isMassOneFormB' r := by
  have hr_lt : r < 2 * 3 ^ 12 :=
    lt_trans (computeNK_lt_uK K r hr) (uK_le_pow12 K hK)
  apply bool_eq_of_iff_true
  constructor
  · intro h
    have : isMassOneForm r := decide_eq_true_eq.mp h
    exact (isMassOneFormB'_iff hr_lt).mpr this
  · intro h
    have : isMassOneForm r := (isMassOneFormB'_iff hr_lt).mp h
    exact decide_eq_true_eq.mpr this

private lemma mass1_in_NK_empty_of_le12 (K : ℕ) (hK : 8 ≤ K ∧ K ≤ 12) :
    mass1_in_NK K = [] := by
  unfold mass1_in_NK
  rw [List.filter_congr (fun r hr => filter_pred_eq_gen (by omega) hr)]
  native_decide

theorem mass1_in_NK_empty_K8  : mass1_in_NK 8  = [] := mass1_in_NK_empty_of_le12 8  (by omega)
theorem mass1_in_NK_empty_K9  : mass1_in_NK 9  = [] := mass1_in_NK_empty_of_le12 9  (by omega)
theorem mass1_in_NK_empty_K10 : mass1_in_NK 10 = [] := mass1_in_NK_empty_of_le12 10 (by omega)
theorem mass1_in_NK_empty_K11 : mass1_in_NK 11 = [] := mass1_in_NK_empty_of_le12 11 (by omega)

-- K=13..16: fast native_decide (binary pow2ModAux)
theorem mass1_in_NK_empty_K13 : mass1_in_NK 13 = [] := by native_decide
theorem mass1_in_NK_empty_K14 : mass1_in_NK 14 = [] := by native_decide
theorem mass1_in_NK_empty_K15 : mass1_in_NK 15 = [] := by native_decide
theorem mass1_in_NK_empty_K16 : mass1_in_NK 16 = [] := by native_decide

-- K=17..25: slow native_decide (deferred to lake build)
theorem mass1_in_NK_empty_K17 : mass1_in_NK 17 = [] := by native_decide
theorem mass1_in_NK_empty_K18 : mass1_in_NK 18 = [] := by native_decide
theorem mass1_in_NK_empty_K19 : mass1_in_NK 19 = [] := by native_decide
theorem mass1_in_NK_empty_K20 : mass1_in_NK 20 = [] := by native_decide
theorem mass1_in_NK_empty_K21 : mass1_in_NK 21 = [] := by native_decide
theorem mass1_in_NK_empty_K22 : mass1_in_NK 22 = [] := by native_decide
theorem mass1_in_NK_empty_K23 : mass1_in_NK 23 = [] := by native_decide
theorem mass1_in_NK_empty_K24 : mass1_in_NK 24 = [] := by native_decide
theorem mass1_in_NK_empty_K25 : mass1_in_NK 25 = [] := by native_decide

theorem mass1_in_NK_empty_K13_25 (K : ℕ) (hK : 13 ≤ K ∧ K ≤ 25) :
    mass1_in_NK K = [] := by
  interval_cases K <;> simp_all [
    mass1_in_NK_empty_K13, mass1_in_NK_empty_K14, mass1_in_NK_empty_K15,
    mass1_in_NK_empty_K16, mass1_in_NK_empty_K17, mass1_in_NK_empty_K18,
    mass1_in_NK_empty_K19, mass1_in_NK_empty_K20, mass1_in_NK_empty_K21,
    mass1_in_NK_empty_K22, mass1_in_NK_empty_K23, mass1_in_NK_empty_K24,
    mass1_in_NK_empty_K25]

/-! ### Trail digit 2 for j ≥ 38 (large convergent index) -/

theorem mass1_j_ge_38_trail2 (K : ℕ) (hK : K ≥ 26) (j : ℕ) (hj : j ≥ 38)
    (ℓ : ℕ) (hℓ : ℓ ≤ 18) (hr : Q Al32 j + ℓ < uK K) :
    hasTrailingDigit2 (pow2Mod (Q Al32 j + ℓ) (3 ^ K)) K = true := by
  by_cases hK35 : K ≥ 35
  · exfalso
    have h38_uk : Q Al32 38 + 18 ≥ uK 35 := by native_decide
    have huk_mono : uK 35 ≤ uK K :=
      Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num : 0 < 3) hK35)
    have hq_bound := Q_mono Al32_hyp (by omega : 1 ≤ j)
      (le_trans (by omega : j ≥ 38) (le_refl 38))
    omega
  · push_neg at hK35
    have hj_max : j ≤ 57 := by
      by_contra h
      push_neg at h
      have hq58 : Q Al32 58 ≥ uK 34 := by native_decide
      have huk_mono : uK K ≤ uK 34 := by
        unfold uK
        have : K - 1 ≤ 33 := by omega
        exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num : 0 < 3) this)
      have hq_mono := Q_mono Al32_hyp (by omega : 1 ≤ 58) (by omega : 58 ≤ j)
      omega
    interval_cases j <;> interval_cases K <;> native_decide

/-! ### Digit extraction helpers -/

private theorem digit_of_mod {val n i : Nat} (hi : i < n) :
    val % 3 ^ n / 3 ^ i % 3 = val / 3 ^ i % 3 := by
  have h3k : 3 ^ n = 3 ^ i * 3 ^ (n - i) := by
    have hn : n = i + (n - i) := by omega
    conv_lhs => rw [hn]
    rw [Nat.pow_add]
  rw [h3k]
  rw [Nat.mod_mul_right_div_self val (3 ^ i) (3 ^ (n - i))]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 3 (by omega : 1 ≤ n - i))

private lemma hasTrailingDigit2_mod_false (val K : Nat) :
    hasTrailingDigit2 val K = false → hasTrailingDigit2 (val % 3 ^ K) K = false := by
  intro h
  unfold hasTrailingDigit2 at h ⊢
  rw [List.any_eq_false] at h ⊢
  intro i hi
  have hiK : i < K := List.mem_range.mp hi
  have hval := h i (List.mem_range.mpr hiK)
  rw [digit_of_mod hiK]
  exact hval

private lemma trail_digit2_subset (val K : ℕ) (hK : K ≥ 1)
    (h : hasTrailingDigit2 val K = false) :
    hasTrailingDigit2 (val % 3 ^ (K - 1)) (K - 1) = false := by
  unfold hasTrailingDigit2 at h ⊢
  rw [List.any_eq_false] at h ⊢
  intro i hi
  have hiK : i < K := List.mem_range.mp (List.mem_range.mpr (by omega))
  have hval := h i (List.mem_range.mpr hiK)
  rw [digit_of_mod (by omega : i < K - 1)]
  exact hval

private lemma trail_digit2_le (val K K0 : ℕ) (hle : K0 ≤ K)
    (h : hasTrailingDigit2 val K = false) :
    hasTrailingDigit2 (val % 3 ^ K0) K0 = false := by
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    by_cases hbase : K0 = K
    · subst hbase; exact hasTrailingDigit2_mod_false val K h
    · have hlt : K0 < K := by omega
      have h1 := trail_digit2_subset val K (by omega) h
      have h2 := ih (K - 1) (by omega) K0 (by omega) h1
      rw [show (val % 3 ^ (K - 1)) % 3 ^ K0 = val % 3 ^ K0 from by
        rw [Nat.mod_mod_of_dvd val (Nat.pow_dvd_pow 3 (le_of_lt hlt))]] at h2
      exact h2

/-! ### computeNK membership implies no trailing digit 2 -/

private lemma computeNK_no_trail2 (K r : ℕ) (hr : r ∈ computeNK K) :
    hasTrailingDigit2 (2 ^ r % 3 ^ K) K = false := by
  unfold computeNK at hr
  rw [List.mem_filter] at hr
  have h := hr.2
  dsimp at h
  cases h_trail : hasTrailingDigit2 (2 ^ r % 3 ^ K) K <;> simp_all

/-! ### Q bound for j ≤ 9 -/

private lemma Q_le_Q9 (j : ℕ) (hj5 : 5 ≤ j) (hj9 : j ≤ 9) :
    Q Al32 j ≤ Q Al32 9 :=
  Q_mono Al32_hyp (by omega) (by omega)

private lemma Q9_plus_18_lt_uK7 : Q Al32 9 + 18 < uK 7 := by native_decide

private lemma Q10_gt_uK9 : Q Al32 10 > uK 9 := by native_decide

/-! ### Main theorem: no new mass-1 elements for K > 7 -/

theorem no_births_after_K7 (K : ℕ) (hK : K > 7) :
    ∀ r, r ∈ computeNK K → isMassOneForm r →
      ∃ p, p ∈ computeNK (K-1) ∧ isMassOneForm p := by
  intro r hr_mem hr_form
  obtain ⟨j, ℓ, hj5, hℓ18, hr⟩ := hr_form
  subst hr
  by_cases hj9 : j ≤ 9
  · -- Case j ≤ 9: r itself is in computeNK (K-1)
    use Q Al32 j + ℓ
    constructor
    · -- Q Al32 j + ℓ ∈ computeNK (K - 1)
      unfold computeNK
      rw [List.mem_filter]
      constructor
      · -- Q Al32 j + ℓ < uK (K - 1)
        have hbound := Q_le_Q9 j hj5 hj9
        have huK : uK 7 ≤ uK (K - 1) := by
          unfold uK; have : 7 ≤ K - 1 := by omega
          exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num : 0 < 3) this)
        omega
      · -- no trailing digit 2
        have htrail := computeNK_no_trail2 K (Q Al32 j + ℓ) hr_mem
        have hsub := trail_digit2_subset (2 ^ (Q Al32 j + ℓ) % 3 ^ K) K (by omega) htrail
        rw [Nat.mod_mod_of_dvd (2 ^ (Q Al32 j + ℓ)) (Nat.pow_dvd_pow 3 (by omega : K - 1 ≤ K))] at hsub
        exact hsub
    · exact ⟨j, ℓ, hj5, hℓ18, rfl⟩
  · -- Case j ≥ 10: derive False
    push_neg at hj9
    exfalso
    by_cases hK9 : K ≤ 9
    · -- K ≤ 9: r ≥ Q(10) > uK(K)
      have hle : uK K ≤ uK 9 := by
        unfold uK; have : K - 1 ≤ 8 := by omega
        exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num : 0 < 3) this)
      have hr_ge : Q Al32 10 ≤ Q Al32 j + ℓ := by
        have hq := Q_mono Al32_hyp (by omega : 1 ≤ 10) (le_of_lt hj9)
        omega
      have hbig := lt_of_lt_of_le Q10_gt_uK9 (le_trans hle (le_of_lt (computeNK_lt_uK K (Q Al32 j + ℓ) hr_mem)))
      omega
    · push_neg at hK9
      by_cases hK12 : K ≤ 12
      · -- K = 10..12: mass1_in_NK_empty_K*
        have hr_form' : isMassOneForm (Q Al32 j + ℓ) := ⟨j, ℓ, hj5, hℓ18, rfl⟩
        unfold mass1_in_NK at *
        have hr_mem' : Q Al32 j + ℓ ∈ (computeNK K).filter (fun x => decide (isMassOneForm x)) :=
          List.mem_filter.mpr ⟨hr_mem, decide_eq_true_eq.mpr hr_form'⟩
        interval_cases K <;> simp_all [mass1_in_NK_empty_K10, mass1_in_NK_empty_K11, mass1_in_NK_empty_K12]
      · push_neg at hK12
        by_cases hK25 : K ≤ 25
        · -- K = 13..25: use placeholder
          have hr_form' : isMassOneForm (Q Al32 j + ℓ) := ⟨j, ℓ, hj5, hℓ18, rfl⟩
          unfold mass1_in_NK at *
          have hr_mem' : Q Al32 j + ℓ ∈ (computeNK K).filter (fun x => decide (isMassOneForm x)) :=
            List.mem_filter.mpr ⟨hr_mem, decide_eq_true_eq.mpr hr_form'⟩
          have hempty := mass1_in_NK_empty_K13_25 K (by omega)
          rw [hempty] at hr_mem'
          exact List.not_mem_nil _ hr_mem'
        · -- K ≥ 26
          push_neg at hK25
          by_cases hj37 : j ≤ 37
          · -- j ≤ 37: r < uK(25), trail digit gives r ∈ computeNK 25
            have hr_val : Q Al32 j + ℓ < uK 25 := by
              have hq_bound := Q_mono Al32_hyp (by omega : 1 ≤ j) (le_trans hj37 (by omega : 37 ≤ 37))
              have hq37 : Q Al32 37 + 18 < uK 25 := by native_decide
              omega
            have htrail_K := computeNK_no_trail2 K (Q Al32 j + ℓ) hr_mem
            have h25_le_K : 25 ≤ K := by omega
            have htrail_25 := trail_digit2_le (2 ^ (Q Al32 j + ℓ) % 3 ^ K) K 25 h25_le_K htrail_K
            rw [Nat.mod_mod_of_dvd (2 ^ (Q Al32 j + ℓ)) (Nat.pow_dvd_pow 3 h25_le_K)] at htrail_25
            have hr_25 : Q Al32 j + ℓ ∈ computeNK 25 := by
              unfold computeNK
              rw [List.mem_filter]
              exact ⟨by omega, htrail_25⟩
            have hr_form' : isMassOneForm (Q Al32 j + ℓ) := ⟨j, ℓ, hj5, hℓ18, rfl⟩
            unfold mass1_in_NK at *
            have hr_mem' : Q Al32 j + ℓ ∈ (computeNK K).filter (fun x => decide (isMassOneForm x)) :=
              List.mem_filter.mpr ⟨hr_mem, decide_eq_true_eq.mpr hr_form'⟩
            have hempty := mass1_in_NK_empty_K13_25 25 (by omega)
            rw [hempty] at hr_mem'
            exact List.not_mem_nil _ hr_mem'
          · -- j ≥ 38: axiom gives trailing digit 2, contradiction
            push_neg at hj37
            have htrail := mass1_j_ge_38_trail2 K (by omega) j (by omega) ℓ hℓ18
            have hlt : Q Al32 j + ℓ < uK K := computeNK_lt_uK K (Q Al32 j + ℓ) hr_mem
            have htrue := htrail hlt
            have hfalse := computeNK_no_trail2 K (Q Al32 j + ℓ) hr_mem
            rw [pow2Mod_eq] at htrue
            simp_all

/-! ### Conditional extinction theorem -/

theorem conditional_extinction (K0 : ℕ) (hK0 : K0 ≥ 12)
    (hempty : mass1_in_NK K0 = [])
    (hno_births : ∀ K, K > K0 →
      ∀ r, r ∈ computeNK K → isMassOneForm r →
        ∃ p, p ∈ computeNK (K-1) ∧ isMassOneForm p) :
    ∀ K, K ≥ K0 → mass1_in_NK K = [] := by
  intro K hK
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    by_cases h : K = K0
    · rw [h]; exact hempty
    · have hK' : K > K0 := by omega
      have hK_prev : K - 1 ≥ K0 := by omega
      have ih_prev := ih (K - 1) (by omega) hK_prev
      unfold mass1_in_NK at ih_prev ⊢
      apply List.filter_eq_nil.mpr
      intro r hr_mem hdec
      have hr_form' : isMassOneForm r := decide_eq_true_eq.mp hdec
      obtain ⟨p, hp_mem, hp_form⟩ := hno_births K hK' r hr_mem hr_form'
      have hp_form_dec : decide (isMassOneForm p) = true := decide_eq_true_eq.mpr hp_form
      have hp_in : p ∈ (computeNK (K-1)).filter (fun x => decide (isMassOneForm x)) :=
        List.mem_filter.mpr ⟨hp_mem, hp_form_dec⟩
      rw [ih_prev] at hp_in
      exact List.not_mem_nil _ hp_in

/-! ### No mass-1 for large K -/

theorem no_mass1_for_large_K (K : ℕ) (hK : K ≥ 12)
    (r : ℕ) (hr : r ∈ computeNK K)
    (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ¬isMassOneForm r := by
  by_contra hform
  have hext := conditional_extinction 12 (by omega) mass1_in_NK_empty_K12
    (fun K hK => no_births_after_K7 K (by omega))
  have hempty := hext K hK
  unfold mass1_in_NK at hempty
  have hr_mem : r ∈ (computeNK K).filter (fun x => decide (isMassOneForm x)) :=
    List.mem_filter.mpr ⟨hr, decide_eq_true_eq.mpr hform⟩
  rw [hempty] at hr_mem
  exact List.not_mem_nil _ hr_mem

end ErdosTernary.Mass1Dynamics
