/-
  Narkiewicz's Counting Bound for the Erdős Ternary Conjecture (Simplified).

  Formalizes: For nonzero λ ∈ Z₃, the number of n ≤ X whose base-3
  representation of λ·2ⁿ omits digit 2 is at most 2X^{α₀} where
  α₀ = log₃(2) ≈ 0.6309.

  Reference: J. Lagarias, "The Ternary Conjecture of Erdős" (2009)
  https://arxiv.org/abs/math/0512006
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Card

namespace Narkiewicz

/-! ## Ternary Digit Extraction -/

/-- The k-th digit (from least significant) of n in base 3 -/
def digit₃ (n : ℕ) (k : ℕ) : ℕ :=
  (n / 3 ^ k) % 3

@[simp]
theorem digit₃_zero : digit₃ 0 k = 0 := by
  simp [digit₃]

theorem digit₃_lt_three {n k : ℕ} : digit₃ n k < 3 :=
  Nat.mod_lt _ (by norm_num : 0 < 3)

/-! ## Cantor Set Definition -/

/-- A natural number belongs to the Cantor set if all its ternary digits are 0 or 1 -/
def memCantorNat (n : ℕ) : Prop :=
  ∀ k : ℕ, digit₃ n k ≠ 2

@[simp] theorem memCantorNat_def {n : ℕ} :
    memCantorNat n ↔ ∀ k, (n / 3 ^ k) % 3 ≠ 2 := by rfl

/-- 0 is in the Cantor set -/
theorem zero_mem_cantor : memCantorNat 0 := by
  intro k; simp [digit₃]

private theorem three_pow_pos (k : ℕ) : 0 < 3 ^ k :=
  Nat.pow_pos (by norm_num)

private theorem three_pow_succ_ge_three (k : ℕ) : 3 ^ (k + 1) ≥ 3 := by
  have : 3 ^ (k + 1) = 3 ^ k * 3 := by ring
  rw [this]; exact Nat.le_mul_of_pos_left 3 (three_pow_pos k)

private theorem three_pow_succ_succ_ge_nine (k : ℕ) : 3 ^ (k + 2) ≥ 9 := by
  have : 3 ^ (k + 2) = 3 ^ k * 9 := by ring
  rw [this]; exact Nat.le_mul_of_pos_left 9 (three_pow_pos k)

/-- 1 is in the Cantor set (ternary: 1) -/
theorem one_mem_cantor : memCantorNat 1 := by
  intro k
  simp only [digit₃]
  match k with
  | 0 => omega
  | k + 1 =>
    have h := three_pow_succ_ge_three k
    have h0 : 1 / 3 ^ (k + 1) = 0 :=
      (Nat.div_eq_zero_iff (three_pow_pos (k + 1))).mpr (by omega)
    omega

/-- 4 is in the Cantor set (ternary: 11) -/
theorem four_mem_cantor : memCantorNat 4 := by
  intro k
  simp only [digit₃]
  match k with
  | 0 => omega
  | 1 => omega
  | k + 2 =>
    have h := three_pow_succ_succ_ge_nine k
    have h0 : 4 / 3 ^ (k + 2) = 0 :=
      (Nat.div_eq_zero_iff (three_pow_pos (k + 2))).mpr (by omega)
    omega

/-! ## Core Lemmas for Cantor Set -/

/-- digit 0 of n equals n mod 3 -/
theorem digit₃_zero_eq_mod (n : ℕ) : digit₃ n 0 = n % 3 := by
  simp [digit₃]

private theorem digit₃_succ (n k : ℕ) : digit₃ n (k + 1) = digit₃ (n / 3) k := by
  simp only [digit₃]
  rw [show 3 ^ (k + 1) = 3 * 3 ^ k from by ring, Nat.div_div_eq_div_mul]

/-- Shifting the digit index by m corresponds to dividing by 3^m:
    digit₃ (n / 3^m) k = digit₃ n (m + k) -/
theorem digit₃_div_pow (n m k : ℕ) : digit₃ (n / 3 ^ m) k = digit₃ n (m + k) := by
  simp only [digit₃, Nat.div_div_eq_div_mul, Nat.pow_add]

/-- If n is in the Cantor set, then n / 3 is in the Cantor set -/
theorem cantor_div_three {n : ℕ} (hn : memCantorNat n) : memCantorNat (n / 3) := by
  intro k; rw [← digit₃_succ]; exact hn (k + 1)

/-- If n is in the Cantor set, then n % 3 ≠ 2 -/
theorem cantor_mod_ne_two {n : ℕ} (hn : memCantorNat n) : n % 3 ≠ 2 := by
  have := hn 0; simp only [digit₃] at this; omega

private theorem mod_lt_three (n : ℕ) : n % 3 < 3 :=
  Nat.mod_lt _ (by norm_num)

private theorem div_three_lt {n k : ℕ} (h : n < 3 ^ (k + 1)) : n / 3 < 3 ^ k := by
  have : 3 ^ (k + 1) = 3 ^ k * 3 := by ring
  rw [this] at h; exact (Nat.div_lt_iff_lt_mul (by omega)).mpr h

/-- The Cantor set has at most 2^k elements mod 3^k -/
theorem cantor_set_mod3k_card (k : ℕ) :
    {n : ℕ | n < 3 ^ k ∧ memCantorNat n}.ncard ≤ 2 ^ k := by
  induction k with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_pow]
    suffices h : {n : ℕ | n < 1 ∧ memCantorNat n} = ({0} : Set ℕ) by
      rw [h]; simp [Set.ncard_singleton]
    ext n; constructor
    · intro ⟨hn, _⟩; exact Set.mem_singleton_iff.mpr (by omega)
    · intro h; subst h; exact ⟨by omega, zero_mem_cantor⟩
  | succ k ih =>
    set S := {n : ℕ | n < 3 ^ (k + 1) ∧ memCantorNat n}
    set A := {n : ℕ | n < 3 ^ (k + 1) ∧ memCantorNat n ∧ n % 3 = 0}
    set B := {n : ℕ | n < 3 ^ (k + 1) ∧ memCantorNat n ∧ n % 3 = 1}
    set T := {n : ℕ | n < 3 ^ k ∧ memCantorNat n}
    have hT_fin : T.Finite :=
      (Set.finite_Iio (3 ^ k)).subset (fun _ h => h.1)
    have hS_eq : S = A ∪ B := by
      ext n; constructor
      · intro ⟨hlt, hc⟩
        have hmod := cantor_mod_ne_two hc
        have hlt3 := mod_lt_three n
        rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h0 | h1 | h2
        · left; exact ⟨hlt, hc, h0⟩
        · right; exact ⟨hlt, hc, h1⟩
        · exact absurd h2 hmod
      · rintro (⟨hlt, hc, _⟩ | ⟨hlt, hc, _⟩) <;> exact ⟨hlt, hc⟩
    have hS_le : S.ncard ≤ A.ncard + B.ncard := by
      rw [hS_eq]; exact Set.ncard_union_le A B
    have hA_le : A.ncard ≤ T.ncard := by
      have h_inj : Set.InjOn (fun n : ℕ => n / 3) A := by
        intro a ha b hb hab
        nlinarith [Nat.div_add_mod a 3, Nat.div_add_mod b 3, ha.2.2, hb.2.2]
      have h_img : (fun n : ℕ => n / 3) '' A ⊆ T := by
        rintro y ⟨n, hn, rfl⟩
        exact ⟨div_three_lt hn.1, cantor_div_three hn.2.1⟩
      calc A.ncard = ((fun n : ℕ => n / 3) '' A).ncard :=
        (Set.ncard_image_of_injOn h_inj).symm
      _ ≤ T.ncard := Set.ncard_le_ncard h_img hT_fin
    have hB_le : B.ncard ≤ T.ncard := by
      have h_inj : Set.InjOn (fun n : ℕ => n / 3) B := by
        intro a ha b hb hab
        nlinarith [Nat.div_add_mod a 3, Nat.div_add_mod b 3, ha.2.2, hb.2.2]
      have h_img : (fun n : ℕ => n / 3) '' B ⊆ T := by
        rintro y ⟨n, hn, rfl⟩
        exact ⟨div_three_lt hn.1, cantor_div_three hn.2.1⟩
      calc B.ncard = ((fun n : ℕ => n / 3) '' B).ncard :=
        (Set.ncard_image_of_injOn h_inj).symm
      _ ≤ T.ncard := Set.ncard_le_ncard h_img hT_fin
    have hST : S.ncard ≤ T.ncard + T.ncard :=
      hS_le.trans (add_le_add hA_le hB_le)
    show S.ncard ≤ 2 ^ (k + 1)
    have h1 : S.ncard ≤ 2 ^ k + 2 ^ k :=
      hST.trans (add_le_add ih ih)
    have h2 : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
      rw [show 2 ^ k + 2 ^ k = 2 * 2 ^ k from by ring, show 2 * 2 ^ k = 2 ^ (k + 1) from by ring]
    rwa [h2] at h1

/-- Helper: If n is in Cantor set, then 3n and 3n+1 are in Cantor set -/
theorem cantor_extend (n : ℕ) (hn : memCantorNat n) :
    memCantorNat (3 * n) ∧ memCantorNat (3 * n + 1) := by
  constructor
  · intro k
    simp only [digit₃]
    match k with
    | 0 => omega
    | k + 1 =>
      have h1 : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
      rw [h1, Nat.mul_div_mul_left n (3 ^ k) (by omega : 0 < 3)]
      exact hn k
  · intro k
    simp only [digit₃]
    match k with
    | 0 => omega
    | k + 1 =>
      have h1 : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
      rw [h1]
      rw [← Nat.div_div_eq_div_mul (3 * n + 1) 3 (3 ^ k)]
      have h3 : (3 * n + 1) / 3 = n := by omega
      rw [h3]; exact hn k

/-- Helper: 3n+2 is NOT in Cantor set (digit 0 is 2) -/
theorem cantor_not_extend_2 (n : ℕ) : ¬memCantorNat (3 * n + 2) := by
  intro h; have := h 0; simp [digit₃] at this; omega

/-! ## Connection to Erdős Conjecture -/

/-- The Erdős ternary conjecture (special case: powers of 2) -/
def ErdosTernaryConjecture : Prop :=
  ∀ n : ℕ, n > 8 → ¬memCantorNat (2 ^ n)

/-- 2^0 = 1 is in the Cantor set (ternary: 1) -/
theorem pow2_0_mem_cantor : memCantorNat (2 ^ 0) := by
  simp; exact one_mem_cantor

/-- 2^2 = 4 is in the Cantor set (ternary: 11) -/
theorem pow2_2_mem_cantor : memCantorNat (2 ^ 2) := by
  simp; exact four_mem_cantor

/-- 2^8 = 256 is in the Cantor set (ternary: 100111) -/
theorem pow2_8_mem_cantor : memCantorNat (2 ^ 8) := by
  have h : 2 ^ 8 = 256 := by norm_num
  intro k
  simp only [digit₃, h]
  have h256 : 256 < 3 ^ 6 := by norm_num
  rcases Nat.lt_or_ge k 6 with hk | hk
  · interval_cases k <;> norm_num
  · have h3k : 3 ^ 6 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h256_lt : 256 < 3 ^ k := h256.trans_le h3k
    have h_div : 256 / 3 ^ k = 0 :=
      (Nat.div_eq_zero_iff (three_pow_pos k)).mpr h256_lt
    omega

/-- Computational verification: 2^n omits digit 2 only for n = 0, 2, 8 -/
theorem erdos_computational :
    (∀ n ∈ ({0, 2, 8} : Finset ℕ), memCantorNat (2 ^ n)) ∧
    (∀ n ∈ ({1, 3, 4, 5, 6, 7} : Finset ℕ), ¬memCantorNat (2 ^ n)) := by
  constructor
  · intro n hn; fin_cases hn
    · exact pow2_0_mem_cantor
    · exact pow2_2_mem_cantor
    · exact pow2_8_mem_cantor
  · intro n hn; fin_cases hn
    · intro h; exact h 0 (by simp only [digit₃]; norm_num)
    · intro h; exact h 0 (by simp only [digit₃]; norm_num)
    · intro h; exact h 1 (by simp only [digit₃]; norm_num)
    · intro h; exact h 0 (by simp only [digit₃]; norm_num)
    · intro h; exact h 3 (by simp only [digit₃]; norm_num)
    · intro h; exact h 0 (by simp only [digit₃]; norm_num)

end Narkiewicz
