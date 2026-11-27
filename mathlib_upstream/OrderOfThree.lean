/-
Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Multiplicity
import Mathlib.GroupTheory.OrderOfElement

/-!
# Multiplicative order of 3 modulo powers of 2 and 2-adic valuation

This file establishes the exact 2-adic valuation (Lifting-the-Exponent) of $3^{2^k} - 1$
and computes the multiplicative order of $3$ in the unit group `(ZMod (2 ^ n))ˣ`.

In `Mathlib.RingTheory.ZMod.UnitsCyclic`, the unit $5$ is formalized as a canonical generator
of the cyclic subgroup of index 2 in `(ZMod (2 ^ n))ˣ`. This module provides the exact
counterpart for $3$, which also has order $2^{n-2}$ for all $n \ge 3$.

## Main results

* `Nat.multiplicity_two_three_pow_two_pow`: For any $k \ge 1$,
  `multiplicity 2 (3 ^ (2 ^ k) - 1) = (k + 2 : ℕ)`.
* `ZMod.orderOf_unitThree`: For any $n \ge 3$,
  `orderOf (ZMod.unitThree n) = 2 ^ (n - 2)`.

## Tags

zmod, units, order, orderOf, lifting the exponent, p-adic valuation
-/

namespace Nat

lemma pow3_pow2_succ (m : ℕ) : 3 ^ (2 ^ (m + 2)) = (3 ^ (2 ^ (m + 1))) ^ 2 := by
  have h : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := by
    rw [Nat.pow_succ, mul_comm]
  rw [h, pow_mul]

private lemma lte_algebra_step (m c : ℕ) :
    let P := 2 ^ (m + 3)
    let u := 1 + 2 * c
    let c' := c + u ^ 2 * 2 ^ (m + 1)
    (1 + P + c * (2 * P)) ^ 2 = 1 + (2 * P) + c' * (4 * P) := by
  intro P u c'
  dsimp [P, u, c']
  ring

/-- The 2-adic Lifting-the-Exponent decomposition for powers of 3:
For all $m \in \mathbb{N}$, $3^{2^{m+1}} = 1 + 2^{m+3} + c \cdot 2^{m+4}$ for some $c \in \mathbb{N}$. -/
theorem pow3_lte_decomp (m : ℕ) :
    ∃ c : ℕ, 3 ^ (2 ^ (m + 1)) = 1 + 2 ^ (m + 3) + c * 2 ^ (m + 4) := by
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

/-- The exact 2-adic valuation of $3^{2^k} - 1$:
For any $k \ge 1$, the multiplicity of 2 in $3^{2^k} - 1$ is exactly $k + 2$. -/
theorem multiplicity_two_three_pow_two_pow (k : ℕ) (hk : 1 ≤ k) :
    multiplicity 2 (3 ^ (2 ^ k) - 1) = (k + 2 : ℕ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  obtain ⟨c, hc⟩ := pow3_lte_decomp m
  have hdecomp : 3 ^ (2 ^ (m + 1)) - 1 = 2 ^ (m + 3) * (1 + 2 * c) := by
    have hP : 2 ^ (m + 4) = 2 ^ (m + 3) * 2 := by rw [Nat.pow_succ]
    rw [hc, hP]
    have h_alg : 1 + 2 ^ (m + 3) + c * (2 ^ (m + 3) * 2) = 1 + 2 ^ (m + 3) * (1 + 2 * c) := by ring
    rw [h_alg, Nat.add_sub_cancel_left]
  have hdvd : 2 ^ (m + 3) ∣ 3 ^ (2 ^ (m + 1)) - 1 := by
    rw [hdecomp]
    exact dvd_mul_right (2 ^ (m + 3)) (1 + 2 * c)
  have hnot_dvd : ¬ 2 ^ (m + 4) ∣ 3 ^ (2 ^ (m + 1)) - 1 := by
    rw [hdecomp]
    intro h
    have h2pow : 2 ^ (m + 4) = 2 ^ (m + 3) * 2 := by rw [Nat.pow_succ]
    rw [h2pow] at h
    have hodd : ¬ 2 ∣ (1 + 2 * c) := by
      intro hdiv
      have : (1 + 2 * c) % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
      omega
    have hdiv_cancel := (Nat.mul_dvd_mul_iff_left (Nat.pos_pow_of_pos (m + 3) (by decide))).mp h
    exact hodd hdiv_cancel
  rw [multiplicity.eq_coe_iff]
  exact ⟨hdvd, hnot_dvd⟩

end Nat

namespace ZMod

lemma natCast_sub_one_eq_zero_iff {m : ℕ} (a : ℕ) (ha : 1 ≤ a) :
    ((a - 1 : ℕ) : ZMod m) = 0 ↔ (a : ZMod m) = 1 := by
  rw [Nat.cast_sub ha, Nat.cast_one, sub_eq_zero]

/-- 3 is coprime to any power of 2. -/
theorem coprime_three_pow_two (n : ℕ) : Nat.Coprime 3 (2 ^ n) := by
  apply Nat.Coprime.pow_right
  decide

/-- The unit 3 in `(ZMod (2 ^ n))ˣ`. -/
def unitThree (n : ℕ) : (ZMod (2 ^ n))ˣ :=
  ZMod.unitOfCoprime 3 (coprime_three_pow_two n)

@[simp]
theorem coe_unitThree (n : ℕ) : ((unitThree n : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) = 3 := rfl

theorem unitThree_pow (n k : ℕ) :
    ((unitThree n ^ k : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) = (3 ^ k : ZMod (2 ^ n)) := by
  push_cast
  rw [coe_unitThree]

/-- The unit 3 raised to the power $2^{n-2}$ is the identity in `(ZMod (2 ^ n))ˣ` for $n \ge 3$. -/
theorem unitThree_pow_two_sub_two_eq_one (n : ℕ) (hn : 3 ≤ n) :
    unitThree n ^ (2 ^ (n - 2)) = 1 := by
  ext
  rw [Units.val_one, unitThree_pow]
  have hk : 1 ≤ n - 2 := by omega
  have hmult := Nat.multiplicity_two_three_pow_two_pow (n - 2) hk
  have heq : (n - 2) + 2 = n := by omega
  rw [heq] at hmult
  have hdvd : 2 ^ n ∣ 3 ^ (2 ^ (n - 2)) - 1 := (multiplicity.eq_coe_iff.mp hmult).1
  have hpos : 1 ≤ 3 ^ (2 ^ (n - 2)) := Nat.one_le_pow (2 ^ (n - 2)) 3 (by decide)
  have hcast : ((3 ^ (2 ^ (n - 2)) : ℕ) : ZMod (2 ^ n)) = (3 : ZMod (2 ^ n)) ^ (2 ^ (n - 2)) := by
    push_cast
    rfl
  rw [← hcast, ← natCast_sub_one_eq_zero_iff (3 ^ (2 ^ (n - 2))) hpos]
  rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
  exact hdvd

/-- For $n \ge 3$, the unit 3 raised to $2^{n-3}$ is NOT the identity in `(ZMod (2 ^ n))ˣ`. -/
theorem unitThree_pow_two_sub_three_ne_one (n : ℕ) (hn : 3 ≤ n) :
    unitThree n ^ (2 ^ (n - 3)) ≠ 1 := by
  intro h
  have hval : ((unitThree n ^ (2 ^ (n - 3)) : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) = 1 := by
    rw [h, Units.val_one]
  rw [unitThree_pow] at hval
  rcases eq_or_lt_of_le hn with rfl | hn_gt
  · -- Case n = 3: 3^(2^0) = 3 ≢ 1 mod 8
    change (3 ^ (2 ^ 0) : ZMod 8) = 1 at hval
    revert hval
    decide
  · -- Case n > 3: n - 3 ≥ 1
    have hk : 1 ≤ n - 3 := by omega
    have hmult := Nat.multiplicity_two_three_pow_two_pow (n - 3) hk
    have heq : (n - 3) + 2 = n - 1 := by omega
    rw [heq] at hmult
    have hnot_dvd := (multiplicity.eq_coe_iff.mp hmult).2
    have hpos : 1 ≤ 3 ^ (2 ^ (n - 3)) := Nat.one_le_pow (2 ^ (n - 3)) 3 (by decide)
    have hcast : ((3 ^ (2 ^ (n - 3)) : ℕ) : ZMod (2 ^ n)) = (3 : ZMod (2 ^ n)) ^ (2 ^ (n - 3)) := by
      push_cast
      rfl
    rw [← hcast, ← natCast_sub_one_eq_zero_iff (3 ^ (2 ^ (n - 3))) hpos] at hval
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at hval
    -- hval : 2 ^ n ∣ 3 ^ (2 ^ (n - 3)) - 1
    -- But hnot_dvd says ¬ 2 ^ (n - 1 + 1) ∣ 3 ^ (2 ^ (n - 3)) - 1, which is ¬ 2 ^ n ∣ ...
    have hsucc : (n - 1) + 1 = n := by omega
    rw [hsucc] at hnot_dvd
    exact hnot_dvd hval

/-- The multiplicative order of 3 in `(ZMod (2 ^ n))ˣ` is exactly $2^{n-2}$ for all $n \ge 3$. -/
theorem orderOf_unitThree (n : ℕ) (hn : 3 ≤ n) :
    orderOf (unitThree n) = 2 ^ (n - 2) := by
  have hdvd_order : orderOf (unitThree n) ∣ 2 ^ (n - 2) :=
    orderOf_dvd_of_pow_eq_one (unitThree_pow_two_sub_two_eq_one n hn)
  obtain ⟨k, hk_le, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd_order
  rcases lt_or_eq_of_le hk_le with hk_lt | rfl
  · -- If k < n - 2, then k ≤ n - 3, so order divides 2^(n-3)
    have hk_le_pred : k ≤ n - 3 := by omega
    have hdvd_pred : orderOf (unitThree n) ∣ 2 ^ (n - 3) := by
      rw [heq]
      exact Nat.pow_dvd_pow 2 hk_le_pred
    have hpow_eq_one := orderOf_dvd_iff_pow_eq_one.mp hdvd_pred
    exact (unitThree_pow_two_sub_three_ne_one n hn hpow_eq_one).elim
  · -- k = n - 2
    exact heq

#print axioms Nat.multiplicity_two_three_pow_two_pow
#print axioms orderOf_unitThree

end ZMod
