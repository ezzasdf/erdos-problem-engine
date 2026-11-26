/-
Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
-/

/-
  ErdosTernary/TimeReversal.lean

  Time-Reversal Duality Theorem for the Ternary Cantor Multiplier Chain SFT:
    P M_{(a, b)} P = M_{(b-a, b)}ᵀ

  Mathematical Architecture:
  1. State Space:
     A state in the chain SFT of order b is a binary vector u : Fin b → Bool.
  2. Bit-Reversal Involution:
     rev (u : State b) : State b := fun i => u ⟨b - 1 - i.1, by omega⟩
     Satisfies rev (rev u) = u.
  3. Shift Condition:
     isShift u v := ∀ k < b - 1, v ⟨k, ...⟩ = u ⟨k + 1, ...⟩
     Satisfies: isShift (rev u) (rev v) ↔ isShift v u.
  4. Constraint Addition Symmetry:
     validCons (u ⟨b-1, ...⟩) (v ⟨a, ...⟩) (v ⟨0, ...⟩) =
     validCons (v ⟨0, ...⟩) (v ⟨a, ...⟩) (u ⟨b-1, ...⟩)
     by commutativity of integer addition: u_{b-1} - v_a + v_0 = v_0 - v_a + u_{b-1}.
  5. Time-Reversal Transition Duality:
     isTransition a b (rev u) (rev v) ↔ isTransition (b - a) b v u.
  6. Boundary Case 2 Reduction:
     For b - a = 1, (a, a + 1) maps bijectively to (1, a + 1).
  7. Characteristic Polynomial Invariance:
     charpoly(M_{(b-a, b)}) = charpoly(M_{(a, b)}) via Matrix.charpoly_reindex
     and det_transpose.
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace ErdosTernary.TimeReversal

open Matrix

/-- A state in the order-b chain SFT: a binary word of length b. -/
abbrev State (b : ℕ) := Fin b → Bool

/-- The bit-reversal involution on states: reverses the bit positions 0 .. b-1. -/
def rev {b : ℕ} (u : State b) : State b :=
  fun i => u ⟨b - 1 - i.1, by omega⟩

/-- The involution property: `rev (rev u) = u`. -/
@[simp]
theorem rev_rev {b : ℕ} (u : State b) : rev (rev u) = u := by
  ext ⟨i, hi⟩
  dsimp [rev]
  apply congr_arg
  apply Fin.ext
  dsimp
  omega

/-- Bit-reversal equivalence (permutation) on State b. -/
def revEquiv (b : ℕ) : State b ≃ State b where
  toFun := rev
  invFun := rev
  left_inv := rev_rev
  right_inv := rev_rev

@[simp]
theorem revEquiv_apply {b : ℕ} (u : State b) : revEquiv b u = rev u := rfl

@[simp]
theorem revEquiv_symm_apply {b : ℕ} (u : State b) : (revEquiv b).symm u = rev u := rfl

/-- Left-shift condition: `v` is obtained by shifting `u` left by one position. -/
def isShift {b : ℕ} (u v : State b) : Prop :=
  ∀ (k : ℕ) (hk : k + 1 < b), v ⟨k, by omega⟩ = u ⟨k + 1, by omega⟩

/-- The shift condition on reversed states (rev u, rev v) is equivalent to
    the reverse shift condition on (v, u). -/
theorem isShift_rev_iff {b : ℕ} (_hb : 2 ≤ b) (u v : State b) :
    isShift (rev u) (rev v) ↔ isShift v u := by
  constructor
  · intro h k hk
    have hj : b - 2 - k + 1 < b := by omega
    have h_shift := h (b - 2 - k) hj
    have eq_v : (rev v) ⟨b - 2 - k, by omega⟩ = v ⟨k + 1, by omega⟩ := by
      dsimp [rev]
      apply congr_arg
      apply Fin.ext
      dsimp
      omega
    have eq_u : (rev u) ⟨b - 2 - k + 1, by omega⟩ = u ⟨k, by omega⟩ := by
      dsimp [rev]
      apply congr_arg
      apply Fin.ext
      dsimp
      omega
    rw [eq_v, eq_u] at h_shift
    exact h_shift.symm
  · intro h k hk
    have hj : b - 2 - k + 1 < b := by omega
    have h_shift := (h (b - 2 - k) hj).symm
    have eq_v : (rev v) ⟨k, by omega⟩ = v ⟨(b - 2 - k) + 1, by omega⟩ := by
      dsimp [rev]
      apply congr_arg
      apply Fin.ext
      dsimp
      omega
    have eq_u : (rev u) ⟨k + 1, by omega⟩ = u ⟨b - 2 - k, by omega⟩ := by
      dsimp [rev]
      apply congr_arg
      apply Fin.ext
      dsimp
      omega
    rw [eq_v, eq_u]
    exact h_shift

/-- Ternary constraint predicate: returns true iff 0 ≤ x - y + z ≤ 1. -/
def validCons (x y z : Bool) : Bool :=
  let s : Int := (if x then 1 else 0) - (if y then 1 else 0) + (if z then 1 else 0)
  decide (0 ≤ s ∧ s ≤ 1)

/-- Algebraic symmetry of the ternary constraint predicate:
    validCons x y z = validCons z y x identically for all booleans x, y, z. -/
theorem validCons_comm (x y z : Bool) :
    validCons x y z = validCons z y x := by
  dsimp [validCons]
  have h_eq : (if x then (1:Int) else 0) - (if y then 1 else 0) + (if z then 1 else 0) =
              (if z then (1:Int) else 0) - (if y then 1 else 0) + (if x then 1 else 0) := by
    ring
  rw [h_eq]

/-- The SFT transition condition for parameters (a, b) with 1 ≤ a < b:
    - State `v` shifts state `u` left by one bit.
    - The boundary constraint validCons z_new z_a z_b = true holds, where:
      z_new = v (b - 1) is the newly appended bit,
      z_a = u (b - a) is the bit at delay a,
      z_b = u 0 is the oldest bit (at delay b). -/
def isTransition (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (u v : State b) : Prop :=
  isShift u v ∧
  validCons (v ⟨b - 1, by omega⟩) (u ⟨b - a, by omega⟩) (u ⟨0, by omega⟩) = true

/-- Time-Reversal Duality Theorem:
    A transition from (rev u) to (rev v) under parameters (a, b) is valid
    if and only if the transition from v to u under parameters (b - a, b) is valid. -/
theorem time_reversal_transition_duality (a b : ℕ) (ha : 1 ≤ a) (hab : a < b)
    (u v : State b) :
    isTransition a b ha hab (rev u) (rev v) ↔
    isTransition (b - a) b (by omega) (by omega) v u := by
  have hb : 2 ≤ b := by omega
  dsimp [isTransition]
  rw [isShift_rev_iff hb u v]
  constructor
  · rintro ⟨hshift, hcons⟩
    refine ⟨hshift, ?_⟩
    have eq_v_new : (rev v) ⟨b - 1, by omega⟩ = v ⟨0, by omega⟩ := by
      dsimp [rev]
      apply congr_arg
      apply Fin.ext
      dsimp
      omega
    have eq_u_a : (rev u) ⟨b - a, by omega⟩ = u ⟨a - 1, by omega⟩ := by
      dsimp [rev]
      apply congr_arg
      apply Fin.ext
      dsimp
      omega
    have eq_u_0 : (rev u) ⟨0, by omega⟩ = u ⟨b - 1, by omega⟩ := rfl
    rw [eq_v_new, eq_u_a, eq_u_0] at hcons
    have h_ua : u ⟨a - 1, by omega⟩ = v ⟨a, by omega⟩ := by
      have h_sh := hshift (a - 1) (by omega)
      have eq_v : v ⟨(a - 1) + 1, by omega⟩ = v ⟨a, by omega⟩ := by
        apply congr_arg
        apply Fin.ext
        dsimp
        omega
      rw [← eq_v]
      exact h_sh
    rw [h_ua] at hcons
    have h_comm := validCons_comm (v ⟨0, by omega⟩) (v ⟨a, by omega⟩) (u ⟨b - 1, by omega⟩)
    rw [h_comm] at hcons
    have eq_va : v ⟨a, by omega⟩ = v ⟨b - (b - a), by omega⟩ := by
      apply congr_arg
      apply Fin.ext
      dsimp
      omega
    rw [eq_va] at hcons
    exact hcons
  · rintro ⟨hshift, hcons⟩
    refine ⟨hshift, ?_⟩
    have eq_va : v ⟨b - (b - a), by omega⟩ = v ⟨a, by omega⟩ := by
      apply congr_arg
      apply Fin.ext
      dsimp
      omega
    rw [eq_va] at hcons
    have h_comm := validCons_comm (u ⟨b - 1, by omega⟩) (v ⟨a, by omega⟩) (v ⟨0, by omega⟩)
    rw [h_comm] at hcons
    have h_ua : u ⟨a - 1, by omega⟩ = v ⟨a, by omega⟩ := by
      have h_sh := hshift (a - 1) (by omega)
      have eq_v : v ⟨(a - 1) + 1, by omega⟩ = v ⟨a, by omega⟩ := by
        apply congr_arg
        apply Fin.ext
        dsimp
        omega
      rw [← eq_v]
      exact h_sh
    rw [← h_ua] at hcons
    have eq_v_new : (rev v) ⟨b - 1, by omega⟩ = v ⟨0, by omega⟩ := by
      dsimp [rev]
      apply congr_arg
      apply Fin.ext
      dsimp
      omega
    have eq_u_a : (rev u) ⟨b - a, by omega⟩ = u ⟨a - 1, by omega⟩ := by
      dsimp [rev]
      apply congr_arg
      apply Fin.ext
      dsimp
      omega
    have eq_u_0 : (rev u) ⟨0, by omega⟩ = u ⟨b - 1, by omega⟩ := rfl
    rw [← eq_v_new, ← eq_u_a, ← eq_u_0] at hcons
    exact hcons

/-- Specialization to Boundary Case 2 (b = a + 1):
    The transition condition for (a, a + 1) under time-reversal maps bijectively
    to the transition condition for (1, a + 1). -/
theorem boundary_case2_reversal_to_boundary_case1 (a : ℕ) (ha : 1 ≤ a) (u v : State (a + 1)) :
    isTransition a (a + 1) ha (by omega) (rev u) (rev v) ↔
    isTransition 1 (a + 1) (by omega) (by omega) v u := by
  have hab : a < a + 1 := by omega
  have h_dual := time_reversal_transition_duality a (a + 1) ha hab u v
  rw [h_dual]
  dsimp [isTransition]
  have eq_v : v ⟨(a + 1) - ((a + 1) - a), by omega⟩ = v ⟨a, by omega⟩ := by
    apply congr_arg
    apply Fin.ext
    dsimp
    omega
  rw [eq_v]

/-- The transition matrix M_{(a, b)} associated with the chain SFT. -/
noncomputable def transitionMatrix (R : Type*) [CommRing R] (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    Matrix (State b) (State b) R :=
  open Classical in
  fun u v => if isTransition a b ha hab u v then 1 else 0

/-- Characteristic matrix transpose lemma: charmatrix (Mᵀ) = (charmatrix M)ᵀ. -/
theorem charmatrix_transpose {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (M : Matrix n n R) : charmatrix Mᵀ = (charmatrix M)ᵀ := by
  ext i j
  dsimp [charmatrix, transpose, scalar, diagonal]
  by_cases h : i = j
  · subst h
    simp
  · have h_ne : j ≠ i := Ne.symm h
    simp [h, h_ne]

/-- Characteristic polynomial transpose invariance: (Mᵀ).charpoly = M.charpoly. -/
theorem charpoly_transpose {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (M : Matrix n n R) : Mᵀ.charpoly = M.charpoly := by
  unfold Matrix.charpoly
  rw [charmatrix_transpose, det_transpose]

/-- The Matrix Time-Reversal Transpose Identity:
    Reindexing M_{(a, b)} by the bit-reversal involution yields M_{(b-a, b)}ᵀ. -/
theorem time_reversal_matrix_transpose (R : Type*) [CommRing R] (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    reindex (revEquiv b) (revEquiv b) (transitionMatrix R a b ha hab) =
    (transitionMatrix R (b - a) b (by omega) (by omega))ᵀ := by
  ext u v
  dsimp [reindex, submatrix, transitionMatrix, transpose]
  rw [time_reversal_transition_duality a b ha hab u v]

/-- The Master Characteristic Polynomial Invariance Theorem:
    The chain SFT transition matrices for (a, b) and (b - a, b) share the identical
    characteristic polynomial. -/
theorem charpoly_time_reversal_invariance (R : Type*) [CommRing R] (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    (transitionMatrix R (b - a) b (by omega) (by omega)).charpoly =
    (transitionMatrix R a b ha hab).charpoly := by
  have h_mat := time_reversal_matrix_transpose R a b ha hab
  rw [← charpoly_transpose]
  rw [← h_mat]
  exact Matrix.charpoly_reindex (revEquiv b) (transitionMatrix R a b ha hab)

/-- Corollary: For Boundary Case 2 (b = a + 1), the characteristic polynomial
    of (a, a + 1) equals that of (1, a + 1).

    Robustness Note: `h_mat` is proved by `rfl` because `Nat.succ a - 1` definitionally
    reduces to `a` in Lean 4.12's `Nat.sub` implementation. If a future Lean version
    modifies `Nat.sub` so that reduction requires propositional equality, replace `rfl`
    with `congrArg (fun x => transitionMatrix R x (a + 1) ... ...) (Nat.succ_sub_one a)`. -/
theorem boundary_case2_charpoly_eq_boundary_case1 (R : Type*) [CommRing R] (a : ℕ) (ha : 1 ≤ a) :
    (transitionMatrix R a (a + 1) ha (by omega)).charpoly =
    (transitionMatrix R 1 (a + 1) (by omega) (by omega)).charpoly := by
  have h := charpoly_time_reversal_invariance R 1 (a + 1) (by omega) (by omega)
  have h_mat : transitionMatrix R a (a + 1) ha (by omega) =
               transitionMatrix R ((a + 1) - 1) (a + 1) (by omega) (by omega) := rfl
  rw [h_mat, h]

end ErdosTernary.TimeReversal
