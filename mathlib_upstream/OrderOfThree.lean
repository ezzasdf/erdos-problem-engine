/-
Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Positivity

/-!
# Multiplicative order of 3 modulo powers of 2 and 2-adic valuation

This file establishes the exact 2-adic valuation (Lifting-the-Exponent) of $3^{2^k} - 1$
and computes the multiplicative order of $3$ in the unit group `(ZMod (2 ^ n))ˣ`.

In `Mathlib.RingTheory.ZMod.UnitsCyclic`, the unit $5$ is formalized as a canonical generator
of the cyclic subgroup of index 2 in `(ZMod (2 ^ n))ˣ`. This module provides the counterpart
for $3$, which also has order $2^{n-2}$ for all $n \ge 3$.

## Main results

* `Nat.multiplicity_two_three_pow_two_pow`: For any $k \ge 1$,
  `multiplicity 2 (3 ^ (2 ^ k) - 1) = k + 2`.
* `ZMod.unitThree`: The unit $3$ in `(ZMod (2 ^ n))ˣ`.
* `ZMod.orderOf_unitThree`: For any $n \ge 3$,
  `orderOf (unitThree : (ZMod (2 ^ n))ˣ) = 2 ^ (n - 2)`.

## Tags

zmod, units, order, orderOf, lifting the exponent, p-adic valuation
-/

namespace Nat

private lemma pow3_pow2_succ (m : ℕ) : 3 ^ (2 ^ (m + 2)) = (3 ^ (2 ^ (m + 1))) ^ 2 := by
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

private theorem pow3_lte_decomp (m : ℕ) :
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

private theorem two_pow_dvd_three_pow_two_pow_sub_one (k : ℕ) (hk : 1 ≤ k) :
    2 ^ (k + 2) ∣ 3 ^ (2 ^ k) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  obtain ⟨c, hc⟩ := pow3_lte_decomp m
  have hdecomp : 3 ^ (2 ^ (m + 1)) - 1 = 2 ^ (m + 3) * (1 + 2 * c) := by
    have hP : 2 ^ (m + 4) = 2 ^ (m + 3) * 2 := by rw [Nat.pow_succ]
    rw [hc, hP]
    have h_alg : 1 + 2 ^ (m + 3) + c * (2 ^ (m + 3) * 2) = 1 + 2 ^ (m + 3) * (1 + 2 * c) := by ring
    rw [h_alg, Nat.add_sub_cancel_left]
  rw [hdecomp]
  exact dvd_mul_right (2 ^ (m + 3)) (1 + 2 * c)

private theorem not_two_pow_succ_dvd_three_pow_two_pow_sub_one (k : ℕ) (hk : 1 ≤ k) :
    ¬ 2 ^ (k + 3) ∣ 3 ^ (2 ^ k) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  obtain ⟨c, hc⟩ := pow3_lte_decomp m
  have hdecomp : 3 ^ (2 ^ (m + 1)) - 1 = 2 ^ (m + 3) * (1 + 2 * c) := by
    have hP : 2 ^ (m + 4) = 2 ^ (m + 3) * 2 := by rw [Nat.pow_succ]
    rw [hc, hP]
    have h_alg : 1 + 2 ^ (m + 3) + c * (2 ^ (m + 3) * 2) = 1 + 2 ^ (m + 3) * (1 + 2 * c) := by ring
    rw [h_alg, Nat.add_sub_cancel_left]
  rw [hdecomp]
  intro h
  have h2pow : 2 ^ (m + 4) = 2 ^ (m + 3) * 2 := by rw [Nat.pow_succ]
  rw [h2pow] at h
  have hodd : ¬ 2 ∣ (1 + 2 * c) := by
    intro hdiv
    have : (1 + 2 * c) % 2 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    omega
  have hpos : 0 < 2 ^ (m + 3) := by positivity
  have hdiv_cancel := (Nat.mul_dvd_mul_iff_left hpos).mp h
  exact hodd hdiv_cancel

/-- The exact 2-adic valuation of $3^{2^k} - 1$:
For any $k \ge 1$, the multiplicity of 2 in $3^{2^k} - 1$ is exactly $k + 2$. -/
theorem multiplicity_two_three_pow_two_pow (k : ℕ) (hk : 1 ≤ k) :
    multiplicity 2 (3 ^ (2 ^ k) - 1) = k + 2 :=
  multiplicity_eq_of_dvd_of_not_dvd
    (two_pow_dvd_three_pow_two_pow_sub_one k hk)
    (not_two_pow_succ_dvd_three_pow_two_pow_sub_one k hk)

end Nat

namespace ZMod

private lemma natCast_sub_one_eq_zero_iff {m : ℕ} (a : ℕ) (ha : 1 ≤ a) :
    ((a - 1 : ℕ) : ZMod m) = 0 ↔ (a : ZMod m) = 1 := by
  rw [Nat.cast_sub ha, Nat.cast_one, sub_eq_zero]

/-- The unit `3` of `ZMod (2 ^ n)`. -/
def unitThree {n : ℕ} : (ZMod (2 ^ n))ˣ :=
  unitOfCoprime 3 (Nat.Coprime.pow_right n (by decide))

@[simp]
theorem coe_unitThree {n : ℕ} : ((unitThree : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) = 3 := rfl

theorem unitThree_pow (n k : ℕ) :
    ((unitThree ^ k : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) = (3 ^ k : ZMod (2 ^ n)) := by
  push_cast
  rw [coe_unitThree]

private theorem unitThree_pow_two_sub_two_eq_one (n : ℕ) (hn : 3 ≤ n) :
    (unitThree : (ZMod (2 ^ n))ˣ) ^ (2 ^ (n - 2)) = 1 := by
  ext
  rw [Units.val_one, unitThree_pow]
  have hk : 1 ≤ n - 2 := by omega
  have hdvd := Nat.two_pow_dvd_three_pow_two_pow_sub_one (n - 2) hk
  have heq : (n - 2) + 2 = n := by omega
  rw [heq] at hdvd
  have hpos : 1 ≤ 3 ^ (2 ^ (n - 2)) := Nat.one_le_pow (2 ^ (n - 2)) 3 (by decide)
  have hcast : ((3 ^ (2 ^ (n - 2)) : ℕ) : ZMod (2 ^ n)) = (3 : ZMod (2 ^ n)) ^ (2 ^ (n - 2)) := by
    push_cast
    rfl
  rw [← hcast, ← natCast_sub_one_eq_zero_iff (3 ^ (2 ^ (n - 2))) hpos]
  rw [ZMod.natCast_eq_zero_iff]
  exact hdvd

private theorem unitThree_pow_two_sub_three_ne_one (n : ℕ) (hn : 3 ≤ n) :
    (unitThree : (ZMod (2 ^ n))ˣ) ^ (2 ^ (n - 3)) ≠ 1 := by
  intro h
  have hval : (((unitThree : (ZMod (2 ^ n))ˣ) ^ (2 ^ (n - 3)) : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n)) = 1 := by
    rw [h, Units.val_one]
  rw [unitThree_pow] at hval
  rcases eq_or_lt_of_le hn with rfl | hn_gt
  · -- Case n = 3: 3^(2^0) = 3 ≢ 1 mod 8
    change (3 ^ (2 ^ 0) : ZMod 8) = 1 at hval
    revert hval
    decide
  · -- Case n > 3: n - 3 ≥ 1
    have hk : 1 ≤ n - 3 := by omega
    have hnot_dvd := Nat.not_two_pow_succ_dvd_three_pow_two_pow_sub_one (n - 3) hk
    have heq : (n - 3) + 3 = n := by omega
    rw [heq] at hnot_dvd
    have hpos : 1 ≤ 3 ^ (2 ^ (n - 3)) := Nat.one_le_pow (2 ^ (n - 3)) 3 (by decide)
    have hcast : ((3 ^ (2 ^ (n - 3)) : ℕ) : ZMod (2 ^ n)) = (3 : ZMod (2 ^ n)) ^ (2 ^ (n - 3)) := by
      push_cast
      rfl
    rw [← hcast, ← natCast_sub_one_eq_zero_iff (3 ^ (2 ^ (n - 3))) hpos] at hval
    rw [ZMod.natCast_eq_zero_iff] at hval
    exact hnot_dvd hval

/-- The multiplicative order of 3 in `(ZMod (2 ^ n))ˣ` is exactly $2^{n-2}$ for all $n \ge 3$. -/
theorem orderOf_unitThree (n : ℕ) (hn : 3 ≤ n) :
    orderOf (unitThree : (ZMod (2 ^ n))ˣ) = 2 ^ (n - 2) := by
  have hdvd_order : orderOf (unitThree : (ZMod (2 ^ n))ˣ) ∣ 2 ^ (n - 2) :=
    orderOf_dvd_of_pow_eq_one (unitThree_pow_two_sub_two_eq_one n hn)
  obtain ⟨k, hk_le, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd_order
  rcases lt_or_eq_of_le hk_le with hk_lt | rfl
  · -- If k < n - 2, then k ≤ n - 3, so order divides 2^(n-3)
    have hk_le_pred : k ≤ n - 3 := by omega
    have hdvd_pred : orderOf (unitThree : (ZMod (2 ^ n))ˣ) ∣ 2 ^ (n - 3) := by
      rw [heq]
      exact Nat.pow_dvd_pow 2 hk_le_pred
    have hpow_eq_one := orderOf_dvd_iff_pow_eq_one.mp hdvd_pred
    exact (unitThree_pow_two_sub_three_ne_one n hn hpow_eq_one).elim
  · -- k = n - 2
    exact heq

#print axioms Nat.multiplicity_two_three_pow_two_pow
#print axioms orderOf_unitThree

end ZMod
