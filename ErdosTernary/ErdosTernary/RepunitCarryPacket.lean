/-
Copyright (c) 2026 The ErdosTernary Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The ErdosTernary Contributors
-/
import Mathlib

/-!
# Carry-Packet Obstruction and Non-Recurrence

This module formalizes the carry-packet obstruction for powers of two in base 3:
1. **The Non-Recurrence Theorem:** For any $s \ge 2$, $1 + 3^s \ne 2^k$.
   The canonical dyadically pure carry configuration considered here is $2101_3 = 64$.
   Consequently, it cannot recur at any separated ternary scale $64(1 + 3^s)$ for $s \ge 2$.
2. **The Quadrupling Carry Automaton on Cantor Inputs:**
   For $x \in C_3, 4x \in C_3$, the carry-propagation automaton has 4 states.
   Its reachable component from the initial state $(c=0, p=0)$ consists of exactly
   2 states, with transition matrix $\begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}$,
   characteristic polynomial $X^2 - X - 1 = 0$, and Perron eigenvalue $\phi = \frac{1+\sqrt{5}}{2} < 2$.
-/

namespace ErdosTernary.RepunitCarryPacket

/-! ## Part 1: Non-Recurrence of Carry Packets (Catalan / 2-Adic Obstruction) -/

/-- Powers of 3 alternate between 1 and 3 mod 8. -/
theorem pow3_mod8 (s : ℕ) : 3 ^ s % 8 = 1 ∨ 3 ^ s % 8 = 3 := by
  induction s with
  | zero => left; rfl
  | succ s ih =>
    cases ih with
    | inl h1 =>
      right
      have hstep : 3 ^ (s + 1) = 3 ^ s * 3 := pow_succ 3 s
      rw [hstep, Nat.mul_mod, h1]
    | inr h3 =>
      left
      have hstep : 3 ^ (s + 1) = 3 ^ s * 3 := pow_succ 3 s
      rw [hstep, Nat.mul_mod, h3]

/-- 1 + 3^s mod 8 is always either 2 or 4. -/
theorem pow3_add_one_mod8 (s : ℕ) : (1 + 3 ^ s) % 8 = 2 ∨ (1 + 3 ^ s) % 8 = 4 := by
  rcases pow3_mod8 s with h | h
  · left
    rw [Nat.add_mod, h]
  · right
    rw [Nat.add_mod, h]

/-- In particular, 1 + 3^s is never divisible by 8. -/
theorem pow3_add_one_mod8_ne_zero (s : ℕ) : (1 + 3 ^ s) % 8 ≠ 0 := by
  rcases pow3_add_one_mod8 s with h | h <;> rw [h] <;> decide

/-- For all k ≥ 3, 2^k is divisible by 8. -/
theorem pow2_mod8_of_ge_three {k : ℕ} (hk : 3 ≤ k) : 2 ^ k % 8 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 3 + m := Nat.exists_eq_add_of_le hk
  have h2 : 2 ^ (3 + m) = 2 ^ 3 * 2 ^ m := pow_add 2 3 m
  have h8 : 2 ^ 3 = 8 := by rfl
  rw [h2, h8, Nat.mul_mod_right]

/-- Non-recurrence theorem: 1 + 3^s is never a power of 2 for any s ≥ 2. -/
theorem pow3_add_one_ne_pow2 {s k : ℕ} (hs : 2 ≤ s) : 1 + 3 ^ s ≠ 2 ^ k := by
  intro h
  by_cases hk : 3 ≤ k
  · have hmod := pow2_mod8_of_ge_three hk
    have h1 : (1 + 3 ^ s) % 8 = 0 := by rw [h, hmod]
    exact pow3_add_one_mod8_ne_zero s h1
  · have hlt : k < 3 := by omega
    have h2k : 2 ^ k ≤ 4 := by
      interval_cases k <;> decide
    have hs3 : 1 + 3 ^ s ≥ 10 := by
      have : 3 ^ 2 ≤ 3 ^ s := Nat.pow_le_pow_right (by decide) hs
      omega
    omega

/-- Non-recurrence corollary: The carry packet 64 = 2101₃ cannot recur at separated
    ternary scales: 64(1 + 3^s) is never a power of 2 for any s ≥ 2. -/
theorem carry_packet_64_non_recurrent {s k : ℕ} (hs : 2 ≤ s) :
    64 * (1 + 3 ^ s) ≠ 2 ^ k := by
  intro h
  have hpos : 0 < 1 + 3 ^ s := by positivity
  have hge : 64 ≤ 64 * (1 + 3 ^ s) := Nat.le_mul_of_pos_right 64 hpos
  rw [h] at hge
  have hk_ge : 6 ≤ k := by
    by_contra hlt
    have : k < 6 := by omega
    have : 2 ^ k < 64 := by
      interval_cases k <;> decide
    omega
  obtain ⟨m, rfl⟩ : ∃ m, k = 6 + m := Nat.exists_eq_add_of_le hk_ge
  have h2k : 2 ^ (6 + m) = 2 ^ 6 * 2 ^ m := pow_add 2 6 m
  have h64 : 2 ^ 6 = 64 := by rfl
  rw [h2k, h64] at h
  have hdiv : 1 + 3 ^ s = 2 ^ m := Nat.eq_of_mul_eq_mul_left (by decide) h
  exact pow3_add_one_ne_pow2 hs hdiv

/-! ## Part 2: The Quadrupling Carry Automaton on Cantor Inputs -/

/-- Carry states for the ternary self-overlap R_{s+1} = 4R_s + 1 = R_s + 3R_s + 1:
    (carry, previous input bit). -/
inductive CarryState : Type
  | s00 : CarryState  -- c = 0, prev = 0
  | s01 : CarryState  -- c = 0, prev = 1
  | s10 : CarryState  -- c = 1, prev = 0
  | s11 : CarryState  -- c = 1, prev = 1
  deriving DecidableEq, Repr

/-- The step transition under input bit a ∈ {0, 1}.
    An output trit 2 produces `none` (illegal transition). -/
def step : CarryState → Fin 2 → Option CarryState
  | .s00, ⟨0, _⟩ => some .s00
  | .s00, ⟨1, _⟩ => some .s01
  | .s01, ⟨0, _⟩ => some .s00
  | .s01, ⟨1, _⟩ => none
  | .s10, ⟨0, _⟩ => some .s00
  | .s10, ⟨1, _⟩ => none
  | .s11, ⟨0, _⟩ => none
  | .s11, ⟨1, _⟩ => some .s11

/-- Reachability predicate: only {s00, s01} are reachable from initial state s00. -/
def isReachable : CarryState → Prop
  | .s00 => True
  | .s01 => True
  | .s10 => False
  | .s11 => False

/-- Invariance: Any admissible step from a reachable state remains in {s00, s01}. -/
theorem step_preserves_reachable (s : CarryState) (a : Fin 2) (s' : CarryState)
    (hs : isReachable s) (hstep : step s a = some s') : isReachable s' := by
  cases s with
  | s00 =>
    rcases a with ⟨a_val, ha⟩
    interval_cases a_val
    · simp [step] at hstep
      rw [← hstep]
      trivial
    · simp [step] at hstep
      rw [← hstep]
      trivial
  | s01 =>
    rcases a with ⟨a_val, ha⟩
    interval_cases a_val
    · simp [step] at hstep
      rw [← hstep]
      trivial
    · simp [step] at hstep
  | s10 => contradiction
  | s11 => contradiction

/-- The characteristic matrix t * I - A for the reachable 2-state automaton. -/
def charMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![t - 1, -1],
    ![-1, t]]

/-- The characteristic polynomial of the reachable carry automaton is X² - X - 1. -/
theorem charMatrix_det (t : ℝ) :
    (charMatrix t).det = t ^ 2 - t - 1 := by
  rw [Matrix.det_fin_two]
  dsimp [charMatrix]
  ring

/-- The golden ratio φ = (1 + √5)/2. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- φ is a root of the characteristic polynomial X² - X - 1 = 0. -/
theorem phi_sq_sub_phi_sub_one : phi ^ 2 - phi - 1 = 0 := by
  dsimp [phi]
  have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [h5]
  ring

/-- The spectral radius satisfies ρ = φ < 2 strictly. -/
theorem phi_lt_two : phi < 2 := by
  dsimp [phi]
  have hlt : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

#print axioms pow3_add_one_ne_pow2
#print axioms carry_packet_64_non_recurrent
#print axioms step_preserves_reachable
#print axioms charMatrix_det
#print axioms phi_sq_sub_phi_sub_one
#print axioms phi_lt_two

end ErdosTernary.RepunitCarryPacket
