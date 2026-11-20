/-
Copyright (c) 2026 The ErdosTernary Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The ErdosTernary Contributors
-/
import Mathlib
import ErdosTernary.RepunitCarryPacket

/-!
# Negative-Power Erdős Analogue and the Gap Lemma

This module formalizes the negative-power analogue of the Erdős ternary problem:
1. **The Gap Lemma:** The coset of odd residues congruent to 1 or 3 modulo 8 has
   maximum gap strictly bounded by 6. Consequently, every integer interval of length
   at least 6 contains an element of this coset.
2. **The Target Interval:** For any reciprocal $1/2^n$ in base 3, a residue $x \in [0, 2^n)$
   generates digit 2 if and only if $3x / 2^n \ge 2$, i.e., $x \ge \text{threshold } n$.
3. **The Multiplicative Order and Subgroup Surjectivity:**
   The Lifting-the-Exponent Lemma establishes $3^{2^{n-2}} \equiv 1 + 2^n \pmod{2^{n+1}}$
   for all $n \ge 3$. Inductively, the cyclic subgroup $\langle 3 \rangle \le (\mathbb{Z}/2^n\mathbb{Z})^\times$
   equals the entire coset $\mathcal{S}_8 = \{x \in [0, 2^n) : x \equiv 1 \text{ or } 3 \pmod 8\}$.
4. **The Negative-Power Theorem:** For all $n \ge 5$, the target interval has length
   greater than 6, guaranteeing the presence of a residue in $\mathcal{S}_8 = \langle 3 \rangle$.
   Combined with explicit verification for small $n$, every negative power $1/2^n$ with $n \ge 4$
   (and $n = 2$) produces the ternary digit 2, while only $n = 1$ ($1/2 = 0.111\dots_3$)
   and $n = 3$ ($1/8 = 0.0101\dots_3$) omit the digit 2.
-/

namespace ErdosTernary.NegativePower

open ErdosTernary.RepunitCarryPacket

/-- The coset of odd residues congruent to 1 or 3 modulo 8. -/
def isCoset13 (x : ℕ) : Prop :=
  x % 8 = 1 ∨ x % 8 = 3

/-- Gap Lemma (local): In any block of 7 consecutive integers {a, a+1, ..., a+6},
    at least one integer belongs to the coset {1, 3} mod 8. -/
theorem exists_coset13_in_range_seven (a : ℕ) : ∃ i ≤ 6, isCoset13 (a + i) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ a = 8 * q + r :=
    ⟨a / 8, a % 8, Nat.mod_lt _ (by decide), (Nat.div_add_mod a 8).symm⟩
  interval_cases r
  · use 1; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 0 + 1) % 8 = 1 := by omega
    left; exact this
  · use 0; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 1 + 0) % 8 = 1 := by omega
    left; exact this
  · use 1; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 2 + 1) % 8 = 3 := by omega
    right; exact this
  · use 0; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 3 + 0) % 8 = 3 := by omega
    right; exact this
  · use 5; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 4 + 5) % 8 = 1 := by omega
    left; exact this
  · use 4; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 5 + 4) % 8 = 1 := by omega
    left; exact this
  · use 3; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 6 + 3) % 8 = 1 := by omega
    left; exact this
  · use 2; refine ⟨by decide, ?_⟩
    dsimp [isCoset13]
    have : (8 * q + 7 + 2) % 8 = 1 := by omega
    left; exact this

/-- Gap Lemma (interval): Any interval [A, B] of length at least 6 contains
    an element of the coset {1, 3} mod 8. -/
theorem exists_coset13_between {A B : ℕ} (h : A + 6 ≤ B) :
    ∃ x, A ≤ x ∧ x ≤ B ∧ isCoset13 x := by
  obtain ⟨i, hi6, hcoset⟩ := exists_coset13_in_range_seven A
  use A + i
  refine ⟨by omega, by omega, hcoset⟩

/-- The base-3 digit produced by residue x < 2^n in the expansion of 1/2^n. -/
def digit3OfResidue (n x : ℕ) : ℕ :=
  (3 * x) / (2 ^ n)

/-- The lower threshold for residue x to produce digit 2 in base 3:
    3x ≥ 2 · 2^n ↔ x ≥ ⌈(2 · 2^n) / 3⌉. -/
def threshold (n : ℕ) : ℕ :=
  (2 * 2 ^ n + 2) / 3

/-- Any residue in [threshold n, 2^n) forces output digit 2. -/
theorem digit3_eq_two_of_mem_target {n x : ℕ}
    (hx1 : threshold n ≤ x) (hx2 : x < 2 ^ n) :
    digit3OfResidue n x = 2 := by
  dsimp [digit3OfResidue]
  have hpos : 0 < 2 ^ n := by positivity
  have hlower : 2 * 2 ^ n ≤ 3 * x := by
    dsimp [threshold] at hx1
    omega
  have hupper : 3 * x < 3 * 2 ^ n := by omega
  have h1 : 2 ≤ (3 * x) / (2 ^ n) := (Nat.le_div_iff_mul_le hpos).mpr hlower
  have h2 : (3 * x) / (2 ^ n) < 3 := (Nat.div_lt_iff_lt_mul hpos).mpr hupper
  omega

/-- For all n ≥ 5, the target interval [threshold n, 2^n - 1] has width at least 6. -/
theorem threshold_add_six_le_pred_pow2 {n : ℕ} (hn : 5 ≤ n) :
    threshold n + 6 ≤ 2 ^ n - 1 := by
  have h2n : 32 ≤ 2 ^ n := by
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  dsimp [threshold]
  omega

/-- Guaranteed intersection: For all n ≥ 5, the target interval contains an element
    of the coset {1, 3} mod 8. -/
theorem exists_target_residue {n : ℕ} (hn : 5 ≤ n) :
    ∃ x, threshold n ≤ x ∧ x < 2 ^ n ∧ isCoset13 x := by
  have hbound := threshold_add_six_le_pred_pow2 hn
  obtain ⟨x, hA, hB, hcoset⟩ := exists_coset13_between hbound
  refine ⟨x, hA, by omega, hcoset⟩

/-! ## Part 2: Multiplicative Order and Subgroup Surjectivity -/

lemma pow3_pow2_succ (m : ℕ) : 3 ^ (2 ^ (m + 2)) = (3 ^ (2 ^ (m + 1))) ^ 2 := by
  have h : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := by
    rw [Nat.pow_succ, mul_comm]
  rw [h, pow_mul]

lemma lte_algebra_step (m c : ℕ) :
    let P := 2 ^ (m + 3)
    let u := 1 + 2 * c
    let c' := c + u ^ 2 * 2 ^ (m + 1)
    (1 + P + c * (2 * P)) ^ 2 = 1 + (2 * P) + c' * (4 * P) := by
  intro P u c'
  dsimp [P, u, c']
  ring

/-- Lifting-the-Exponent decomposition: For all m, 3^(2^(m+1)) = 1 + 2^(m+3) + c * 2^(m+4). -/
theorem pow3_lte_decomp (m : ℕ) : ∃ c : ℕ, 3 ^ (2 ^ (m + 1)) = 1 + 2 ^ (m + 3) + c * 2 ^ (m + 4) := by
  induction m with
  | zero =>
    use 0
    decide
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    let u := 1 + 2 * c
    let c' := c + u ^ 2 * 2 ^ (m + 1)
    use c'
    rw [pow3_pow2_succ m, hc]
    have hP2 : 2 ^ (m + 4) = 2 * 2 ^ (m + 3) := by
      rw [Nat.pow_succ, mul_comm]
    have hP4 : 2 ^ (m + 5) = 4 * 2 ^ (m + 3) := by
      have : 2 ^ (m + 5) = 2 ^ (m + 3) * 2 ^ 2 := by
        have : m + 5 = (m + 3) + 2 := by omega
        rw [this, Nat.pow_add]
      rw [this]
      ring
    rw [hP2, hP4]
    exact lte_algebra_step m c

lemma pow3_mod2 (k : ℕ) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]

lemma pow3_odd (k : ℕ) : ∃ j, 3 ^ k = 2 * j + 1 := by
  have h := Nat.div_add_mod (3 ^ k) 2
  rw [pow3_mod2 k] at h
  exact ⟨(3 ^ k) / 2, h.symm⟩

/-- Shift identity: 3^(k + 2^(n-2)) = 3^k + 2^n modulo 2^(n+1). -/
theorem pow3_shift_decomp (n k : ℕ) (hn : 3 ≤ n) :
    ∃ C : ℕ, 3 ^ (k + 2 ^ (n - 2)) = 3 ^ k + 2 ^ n + C * 2 ^ (n + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, n = 3 + m := Nat.exists_eq_add_of_le hn
  have h2n : n - 2 = m + 1 := by omega
  have h2np1 : 2 ^ (n + 1) = 2 * 2 ^ (m + 3) := by
    have : n + 1 = (m + 3) + 1 := by omega
    rw [this, Nat.pow_succ, mul_comm]
  have h2nm3 : 2 ^ n = 2 ^ (m + 3) := by
    have : n = m + 3 := by omega
    rw [this]
  obtain ⟨c, hc⟩ := pow3_lte_decomp m
  obtain ⟨j, hj⟩ := pow3_odd k
  rw [h2n]
  have hpow : 3 ^ (k + 2 ^ (m + 1)) = 3 ^ k * 3 ^ (2 ^ (m + 1)) := pow_add 3 k (2 ^ (m + 1))
  rw [hpow, hc]
  use (j + 3 ^ k * c)
  have h2pow : 2 ^ (m + 4) = 2 * 2 ^ (m + 3) := by
    rw [Nat.pow_succ, mul_comm]
  rw [h2pow, h2np1, h2nm3]
  have hj2 : 3 ^ k * 2 ^ (m + 3) = j * (2 * 2 ^ (m + 3)) + 2 ^ (m + 3) := by
    rw [hj]
    ring
  calc
    3 ^ k * (1 + 2 ^ (m + 3) + c * (2 * 2 ^ (m + 3)))
      = 3 ^ k + 3 ^ k * 2 ^ (m + 3) + 3 ^ k * c * (2 * 2 ^ (m + 3)) := by ring
    _ = 3 ^ k + (j * (2 * 2 ^ (m + 3)) + 2 ^ (m + 3)) + 3 ^ k * c * (2 * 2 ^ (m + 3)) := by rw [hj2]
    _ = 3 ^ k + 2 ^ (m + 3) + (j + 3 ^ k * c) * (2 * 2 ^ (m + 3)) := by ring

theorem pow3_shift_mod (n k : ℕ) (hn : 3 ≤ n) :
    3 ^ (k + 2 ^ (n - 2)) % 2 ^ (n + 1) = (3 ^ k + 2 ^ n) % 2 ^ (n + 1) := by
  obtain ⟨C, hC⟩ := pow3_shift_decomp n k hn
  rw [hC]
  have : 3 ^ k + 2 ^ n + C * 2 ^ (n + 1) = (3 ^ k + 2 ^ n) + 2 ^ (n + 1) * C := by ring
  rw [this, Nat.add_mul_mod_self_left]

lemma mod_eight_eq_of_dvd_eight {n : ℕ} (hn : 3 ≤ n) (y : ℕ) :
    (y % 2 ^ n) % 8 = y % 8 := by
  have hdvd : 8 ∣ 2 ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    have : 2 ^ (3 + m) = 2 ^ 3 * 2 ^ m := pow_add 2 3 m
    rw [this]
    exact dvd_mul_right 8 (2 ^ m)
  exact Nat.mod_mod_of_dvd y hdvd

lemma eq_or_eq_add_pow2 {n z x : ℕ} (hz : z < 2 ^ (n + 1)) (hx : z % 2 ^ n = x) :
    z = x ∨ z = x + 2 ^ n := by
  have : z / 2 ^ n < 2 := by
    have : z < 2 ^ n * 2 := by
      have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ, mul_comm]
      rwa [← h2]
    exact Nat.div_lt_of_lt_mul this
  have hz_decomp := (Nat.div_add_mod z (2 ^ n)).symm
  rw [hx] at hz_decomp
  interval_cases z / 2 ^ n
  · left; omega
  · right; omega

lemma shift_mod_eq (k p : ℕ) :
    (3 ^ k + 2 ^ p) % 2 ^ (p + 1) = (3 ^ k % 2 ^ (p + 1) + 2 ^ p) % 2 ^ (p + 1) := by
  have : (3 ^ k + 2 ^ p) % 2 ^ (p + 1) = (3 ^ k % 2 ^ (p + 1) + 2 ^ p % 2 ^ (p + 1)) % 2 ^ (p + 1) := by
    rw [Nat.add_mod]
  rw [this]
  have hlt : 2 ^ p < 2 ^ (p + 1) := by
    have : 2 ^ (p + 1) = 2 ^ p * 2 := by rw [Nat.pow_succ, mul_comm]
    omega
  rw [Nat.mod_eq_of_lt hlt]

/-- Subgroup surjectivity: The orbit ⟨3⟩ mod 2^n traverses all residues in [0, 2^n)
    congruent to 1 or 3 mod 8. -/
theorem pow3_orbit_surj :
    ∀ (n : ℕ), 3 ≤ n → ∀ (x : ℕ), x < 2 ^ n → isCoset13 x → ∃ k, 3 ^ k % 2 ^ n = x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn x hx hcoset
    rcases eq_or_lt_of_le hn with rfl | hn_gt
    · dsimp [isCoset13] at hcoset
      have hxmod : x % 8 = x := Nat.mod_eq_of_lt (by omega)
      rw [hxmod] at hcoset
      rcases hcoset with rfl | rfl
      · use 0; decide
      · use 1; decide
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      have hp3 : 3 ≤ p := by omega
      let x0 := x % 2 ^ p
      have hx0_lt : x0 < 2 ^ p := Nat.mod_lt x (by positivity)
      have hcoset_x0 : isCoset13 x0 := by
        dsimp [isCoset13] at hcoset ⊢
        rwa [mod_eight_eq_of_dvd_eight hp3]
      have hlt : p < p + 1 := Nat.lt_succ_self p
      obtain ⟨k, hk⟩ := ih p hlt hp3 x0 hx0_lt hcoset_x0
      let r := 3 ^ k % 2 ^ (p + 1)
      have hr_lt : r < 2 ^ (p + 1) := Nat.mod_lt _ (by positivity)
      have hr_mod : r % 2 ^ p = x0 := by
        dsimp [r]
        have hdvd : 2 ^ p ∣ 2 ^ (p + 1) := ⟨2, by rw [Nat.pow_succ, mul_comm]⟩
        rw [Nat.mod_mod_of_dvd _ hdvd, hk]
      have hx_cases : x = x0 ∨ x = x0 + 2 ^ p := eq_or_eq_add_pow2 hx rfl
      have hr_cases : r = x0 ∨ r = x0 + 2 ^ p := eq_or_eq_add_pow2 hr_lt hr_mod
      by_cases h : r = x
      · use k
      · use (k + 2 ^ (p - 2))
        rw [pow3_shift_mod p k hp3, shift_mod_eq k p]
        change (r + 2 ^ p) % 2 ^ (p + 1) = x
        rcases hx_cases with hx_eq | hx_eq <;> rcases hr_cases with hr_eq | hr_eq
        · rw [hx_eq, hr_eq] at h
          contradiction
        · rw [hx_eq, hr_eq]
          have : (x0 + 2 ^ p + 2 ^ p) = x0 + 2 ^ (p + 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · rw [hx_eq, hr_eq]
          exact Nat.mod_eq_of_lt (by omega)
        · rw [hx_eq, hr_eq] at h
          contradiction

/-- Orbit Target Intersection: For all n ≥ 5, the cyclic orbit of 3 mod 2^n
    visits the target interval [threshold n, 2^n). -/
theorem exists_target_pow3 {n : ℕ} (hn : 5 ≤ n) :
    ∃ k, threshold n ≤ 3 ^ k % 2 ^ n ∧ 3 ^ k % 2 ^ n < 2 ^ n := by
  obtain ⟨x, hA, hB, hcoset⟩ := exists_target_residue hn
  have hn3 : 3 ≤ n := by omega
  obtain ⟨k, hk⟩ := pow3_orbit_surj n hn3 x hB hcoset
  use k
  rw [hk]
  exact ⟨hA, hB⟩

/-! ## Part 3: Negative-Power Erdős Classification -/

/-- For all n ≥ 5, the ternary expansion of 1/2^n contains digit 2. -/
theorem negative_power_has_digit2_of_ge_five {n : ℕ} (hn : 5 ≤ n) :
    ∃ k, digit3OfResidue n (3 ^ k % 2 ^ n) = 2 := by
  obtain ⟨k, hlower, hupper⟩ := exists_target_pow3 hn
  use k
  exact digit3_eq_two_of_mem_target hlower hupper

/-- Small cases: explicit verification that digit 2 appears for n = 2 and n = 4. -/
theorem digit3_two_at_n2 : digit3OfResidue 2 (3 ^ 1 % 4) = 2 := by
  decide

theorem digit3_two_at_n4 : digit3OfResidue 4 (3 ^ 3 % 16) = 2 := by
  decide

/-- Small cases: n = 1 (1/2) and n = 3 (1/8) avoid digit 2. -/
theorem no_digit2_at_n1 (x : ℕ) (hx : x < 2 ^ 1) : digit3OfResidue 1 x ≠ 2 := by
  interval_cases x <;> decide

theorem no_digit2_at_n3 (k : ℕ) : digit3OfResidue 3 (3 ^ k % 8) ≠ 2 := by
  have h3 := pow3_mod8 k
  rcases h3 with h | h
  · dsimp [digit3OfResidue]
    rw [h]; decide
  · dsimp [digit3OfResidue]
    rw [h]; decide

/-- The Negative-Power Theorem: For all n ≥ 4, the ternary expansion of 1/2^n contains digit 2. -/
theorem negative_power_has_digit2 (n : ℕ) (hn : 4 ≤ n) :
    ∃ k, digit3OfResidue n (3 ^ k % 2 ^ n) = 2 := by
  rcases eq_or_lt_of_le hn with rfl | hgt
  · use 3
    exact digit3_two_at_n4
  · exact negative_power_has_digit2_of_ge_five hgt

#print axioms exists_coset13_in_range_seven
#print axioms exists_coset13_between
#print axioms digit3_eq_two_of_mem_target
#print axioms threshold_add_six_le_pred_pow2
#print axioms exists_target_residue
#print axioms pow3_lte_decomp
#print axioms pow3_shift_decomp
#print axioms pow3_shift_mod
#print axioms pow3_orbit_surj
#print axioms exists_target_pow3
#print axioms negative_power_has_digit2_of_ge_five
#print axioms digit3_two_at_n2
#print axioms digit3_two_at_n4
#print axioms no_digit2_at_n1
#print axioms no_digit2_at_n3
#print axioms negative_power_has_digit2

end ErdosTernary.NegativePower
