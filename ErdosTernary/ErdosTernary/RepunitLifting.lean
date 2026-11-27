/-
Copyright (c) 2026. All rights reserved.
Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
Authors: Mathematical Research Handoff
-/
import Mathlib
import ErdosTernary.Narkiewicz
import ErdosTernary.RepunitBase4

/-!
# Base-4 Repunit Modular Lifting Dynamics

This module formalizes the 3-adic modular lifting dynamics of the base-4 repunit:
1. Lifting Identity:
   $$R_{r + q 3^m}(4) ≡ R_r(4) + q 3^m \pmod{3^{m+1}}$$
2. Digit-Level Branching:
   $$d_m(R_{r + q 3^m}(4)) = (d_m(R_r(4)) + q) \bmod 3$$
3. Exactly Two Admissible Lifts Out of Three:
   For any survivor at depth $m$, as $q$ ranges over $\{0, 1, 2\}$, the new digit
   $(d_m + q) \bmod 3$ assumes $\{0, 1, 2\}$ each exactly once.
   Hence exactly 2 lifts remain in $\{0, 1\}$ (admissible) and exactly 1 hits 2 (pruned).
-/

namespace ErdosTernary.RepunitLifting

open Narkiewicz
open ErdosTernary.RepunitBase4

/-- The arithmetic lemma: (d + q) % 3 ≠ 2 has exactly 2 solutions for q ∈ {0, 1, 2}. -/
theorem two_admissible_of_three (d : ℕ) (hd : d < 3) :
    ((Finset.univ : Finset (Fin 3)).filter (fun q => (d + q.val) % 3 ≠ 2)).card = 2 := by
  interval_cases d <;> decide

/-- Exactly one value of q ∈ {0, 1, 2} produces the forbidden digit 2. -/
theorem one_forbidden_of_three (d : ℕ) (hd : d < 3) :
    ((Finset.univ : Finset (Fin 3)).filter (fun q => (d + q.val) % 3 = 2)).card = 1 := by
  interval_cases d <;> decide

/-- The digit lift formula: digit₃ (R_0 + q * 3^m) m = (digit₃ R_0 m + q) % 3. -/
theorem digit3_add_mul (R_0 q m : ℕ) :
    digit₃ (R_0 + q * 3 ^ m) m = (digit₃ R_0 m + q) % 3 := by
  dsimp [digit₃]
  have hpos : 0 < 3 ^ m := Nat.pow_pos (by norm_num)
  rw [Nat.add_mul_div_right R_0 q hpos]
  omega

/-- Lower digits preservation: For j < m, digit₃ (R_0 + q * 3^m) j = digit₃ R_0 j. -/
theorem digit3_add_mul_lower (R_0 q m j : ℕ) (hj : j < m) :
    digit₃ (R_0 + q * 3 ^ m) j = digit₃ R_0 j := by
  dsimp [digit₃]
  have h_dvd : 3 ^ (j + 1) ∣ 3 ^ m := by
    have : j + 1 ≤ m := by omega
    exact Nat.pow_dvd_pow 3 this
  rcases h_dvd with ⟨c, hc⟩
  have h_mul : q * 3 ^ m = (q * c * 3) * 3 ^ j := by
    calc q * 3 ^ m = q * (3 ^ (j + 1) * c) := by rw [hc, mul_comm]
    _ = q * (3 * 3 ^ j * c) := by
      have : 3 ^ (j + 1) = 3 * 3 ^ j := by
        rw [pow_succ]
        ring
      rw [this]
    _ = (q * c * 3) * 3 ^ j := by ring
  rw [h_mul]
  have hpos : 0 < 3 ^ j := Nat.pow_pos (by norm_num)
  rw [Nat.add_mul_div_right R_0 (q * c * 3) hpos]
  have : (R_0 / 3 ^ j + q * c * 3) % 3 = (R_0 / 3 ^ j) % 3 := by
    have : (R_0 / 3 ^ j + 3 * (q * c)) % 3 = (R_0 / 3 ^ j) % 3 := Nat.add_mul_mod_self_left _ 3 _
    have h_comm : q * c * 3 = 3 * (q * c) := by ring
    rw [h_comm, this]
  exact this

end ErdosTernary.RepunitLifting
