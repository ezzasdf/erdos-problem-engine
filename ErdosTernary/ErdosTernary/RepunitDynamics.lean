/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathematical Research Handoff
-/
import Mathlib
import ErdosTernary.Narkiewicz
import ErdosTernary.RepunitBase4

namespace ErdosTernary.RepunitDynamics

open Narkiewicz
open ErdosTernary.RepunitBase4

/-- The exact recurrence relation: R_{s+1}(4) = 4 * R_s(4) + 1. -/
theorem repunit4_succ (s : ℕ) : repunit4 (s + 1) = 4 * repunit4 s + 1 := by
  have h1 := pow4_eq_three_mul_repunit (s + 1)
  have h0 := pow4_eq_three_mul_repunit s
  have hpow : 4 ^ (s + 1) = 4 * 4 ^ s := by rw [pow_succ, mul_comm]
  rw [hpow, h0] at h1
  omega

/-- The affine dynamical map T(y) = 4y + 1 on ℕ. -/
def T (y : ℕ) : ℕ := 4 * y + 1

/-- Dynamical recurrence: R_{s+1}(4) = T (repunit4 s). -/
theorem repunit4_succ_eq_T (s : ℕ) : repunit4 (s + 1) = T (repunit4 s) :=
  repunit4_succ s

/-- Base case: R_0(4) = 0. -/
theorem repunit4_zero : repunit4 0 = 0 := rfl

/-- Iterated dynamics: The repunit R_s(4) is the s-th iterate of T applied to 0. -/
theorem repunit4_eq_iterate_T (s : ℕ) : repunit4 s = (T^[s]) 0 := by
  induction s with
  | zero => rfl
  | succ n ih =>
    rw [repunit4_succ_eq_T, ih]
    exact (Function.iterate_succ' T n).symm ▸ rfl

/-- Dynamical conjugacy modulo 3^m:
    R_{s+1}(4) ≡ 4 * R_s(4) + 1 (mod 3^m). -/
theorem repunit4_mod_succ (s m : ℕ) :
    repunit4 (s + 1) % 3 ^ m = (4 * (repunit4 s % 3 ^ m) + 1) % 3 ^ m := by
  rw [repunit4_succ s]
  have h1 : (4 * repunit4 s + 1) % 3 ^ m = ((4 * repunit4 s) % 3 ^ m + 1 % 3 ^ m) % 3 ^ m :=
    Nat.add_mod (4 * repunit4 s) 1 (3 ^ m)
  have h2 : (4 * (repunit4 s % 3 ^ m) + 1) % 3 ^ m = ((4 * (repunit4 s % 3 ^ m)) % 3 ^ m + 1 % 3 ^ m) % 3 ^ m :=
    Nat.add_mod (4 * (repunit4 s % 3 ^ m)) 1 (3 ^ m)
  have h3 : (4 * repunit4 s) % 3 ^ m = (4 * (repunit4 s % 3 ^ m)) % 3 ^ m := by
    have ha : (4 * repunit4 s) % 3 ^ m = ((4 % 3 ^ m) * (repunit4 s % 3 ^ m)) % 3 ^ m :=
      Nat.mul_mod 4 (repunit4 s) (3 ^ m)
    have hb : (4 * (repunit4 s % 3 ^ m)) % 3 ^ m = ((4 % 3 ^ m) * (repunit4 s % 3 ^ m % 3 ^ m)) % 3 ^ m :=
      Nat.mul_mod 4 (repunit4 s % 3 ^ m) (3 ^ m)
    rw [Nat.mod_mod] at hb
    rw [ha, hb]
  rw [h1, h2, h3]

/-- Projective compatibility: For m₁ ≤ m₂, the projection from depth m₂ to m₁
    commutes with the repunit evaluation modulo 3^m. -/
theorem repunit4_mod_compat (s m₁ m₂ : ℕ) (hle : m₁ ≤ m₂) :
    (repunit4 s % 3 ^ m₂) % 3 ^ m₁ = repunit4 s % 3 ^ m₁ := by
  have hdvd : 3 ^ m₁ ∣ 3 ^ m₂ := Nat.pow_dvd_pow 3 hle
  exact Nat.mod_mod_of_dvd (repunit4 s) hdvd

end ErdosTernary.RepunitDynamics
