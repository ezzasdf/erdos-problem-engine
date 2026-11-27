/-
Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
-/

/-
  ErdosTernary/PeriodicOrbit.lean

  Formalization of the Universal Periodic Orbit & SFT Component Primitivity (Track B):
  1. All-Zero and All-One States:
     - allZeros b : State b := fun _ => false (0ᵇ)
     - allOnes b : State b := fun _ => true (1ᵇ)
  2. Self-Loops:
     - 0ᵇ → 0ᵇ is a valid transition for all 1 ≤ a < b (cycle of length 1).
     - 1ᵇ → 1ᵇ is a valid transition for all 1 ≤ a < b (cycle of length 1).
  3. Reachability Path 0ᵇ → 1ᵇ:
     - Explicit interpolation states state01 b k for k = 0 .. b.
     - Every step k → k + 1 satisfies validCons 1 z_a 0 = true since 1 - z_a + 0 ∈ {0, 1}.
     - Hence 0ᵇ reaches 1ᵇ in exactly b steps.
  4. Reachability Path 1ᵇ → 0ᵇ:
     - Explicit interpolation states state10 b k for k = 0 .. b.
     - Every step k → k + 1 satisfies validCons 0 z_a 1 = true since 0 - z_a + 1 ∈ {0, 1}.
     - Hence 1ᵇ reaches 0ᵇ in exactly b steps.
  5. Strongly Connected Component (SCC) & Aperiodicity:
     - 0ᵇ and 1ᵇ lie in the same Strongly Connected Component (mutual reachability).
     - Because 0ᵇ has a self-loop (cycle length 1), the SCC has period gcd(1, 2b) = 1.
     - Thus the maximal recurrent component R containing 0ᵇ and 1ᵇ is primitive.
  6. Universal Alternating 2b-Periodic Sequence:
     - z_i = 1_{(i mod 2b) ≥ b} satisfies z_{i-b} = 1 - z_i identically on ℤ.
     - Constraint: z_i - z_{i-a} + z_{i-b} = 1 - z_{i-a} ∈ {0, 1} for all i ∈ ℤ.
     - Embeds both non-extremizer witness words w_* into the primitive component R.
-/

import ErdosTernary.TimeReversal
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

namespace ErdosTernary.PeriodicOrbit

open ErdosTernary.TimeReversal

/-- The all-zero state 0ᵇ. -/
def allZeros (b : ℕ) : State b := fun _ => false

/-- The all-one state 1ᵇ. -/
def allOnes (b : ℕ) : State b := fun _ => true

/-- The all-zero state has a valid self-loop 0ᵇ → 0ᵇ for all 1 ≤ a < b. -/
theorem allZeros_self_loop (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    isTransition a b ha hab (allZeros b) (allZeros b) := by
  dsimp [isTransition, isShift, allZeros, validCons]
  refine ⟨by intros; rfl, ?_⟩
  decide

/-- The all-one state has a valid self-loop 1ᵇ → 1ᵇ for all 1 ≤ a < b. -/
theorem allOnes_self_loop (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    isTransition a b ha hab (allOnes b) (allOnes b) := by
  dsimp [isTransition, isShift, allOnes, validCons]
  refine ⟨by intros; rfl, ?_⟩
  decide

/-- State 0ᵇ with k ones appended from the right:
    bit i is true iff i ≥ b - k.
    For k = 0, this is 0ᵇ. For k = b, this is 1ᵇ. -/
def state01 (b : ℕ) (k : ℕ) : State b :=
  fun i => decide (b - k ≤ i.1)

@[simp]
theorem state01_zero (b : ℕ) : state01 b 0 = allZeros b := by
  ext ⟨i, hi⟩
  dsimp [state01, allZeros]
  have : ¬ (b - 0 ≤ i) := by omega
  exact decide_eq_false this

@[simp]
theorem state01_self (b : ℕ) : state01 b b = allOnes b := by
  ext ⟨i, hi⟩
  dsimp [state01, allOnes]
  have : b - b ≤ i := by omega
  exact decide_eq_true this

/-- The shift condition holds from state01 b k to state01 b (k + 1). -/
theorem state01_shift (b : ℕ) (k : ℕ) (hk : k < b) :
    isShift (state01 b k) (state01 b (k + 1)) := by
  intro j hj
  dsimp [state01]
  have h_iff : b - (k + 1) ≤ j ↔ b - k ≤ j + 1 := by omega
  simp only [h_iff]

/-- Key constraint satisfaction: appending a 1 to a state whose oldest bit is 0
    always satisfies the ternary chain constraint validCons 1 z_a 0 = true,
    because 1 - z_a + 0 = 1 - z_a ∈ {0, 1}. -/
theorem validCons_one_any_zero (z_a : Bool) :
    validCons true z_a false = true := by
  cases z_a <;> decide

/-- Symmetrically, appending a 0 to a state whose oldest bit is 1
    always satisfies the ternary chain constraint validCons 0 z_a 1 = true,
    because 0 - z_a + 1 = 1 - z_a ∈ {0, 1}. -/
theorem validCons_zero_any_one (z_a : Bool) :
    validCons false z_a true = true := by
  cases z_a <;> decide

/-- Step transition lemma: for every k < b, the transition from
    state01 b k to state01 b (k + 1) is valid in the chain SFT. -/
theorem state01_step_valid (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (k : ℕ) (hk : k < b) :
    isTransition a b ha hab (state01 b k) (state01 b (k + 1)) := by
  refine ⟨state01_shift b k hk, ?_⟩
  dsimp [validCons]
  have h_new : state01 b (k + 1) ⟨b - 1, by omega⟩ = true := by
    dsimp [state01]
    have : b - (k + 1) ≤ b - 1 := by omega
    simp [this]
  have h_old : state01 b k ⟨0, by omega⟩ = false := by
    dsimp [state01]
    have : ¬ (b - k ≤ 0) := by omega
    simp [this]
  rw [h_new, h_old]
  exact validCons_one_any_zero (state01 b k ⟨b - a, by omega⟩)

/-- Symmetrically: state 1ᵇ with k zeros appended from the right. -/
def state10 (b : ℕ) (k : ℕ) : State b :=
  fun i => decide (i.1 < b - k)

@[simp]
theorem state10_zero (b : ℕ) : state10 b 0 = allOnes b := by
  ext ⟨i, hi⟩
  dsimp [state10, allOnes]
  have : i < b - 0 := hi
  exact decide_eq_true this

@[simp]
theorem state10_self (b : ℕ) : state10 b b = allZeros b := by
  ext ⟨i, hi⟩
  dsimp [state10, allZeros]
  have : ¬ (i < b - b) := by omega
  exact decide_eq_false this

theorem state10_shift (b : ℕ) (k : ℕ) (hk : k < b) :
    isShift (state10 b k) (state10 b (k + 1)) := by
  intro j hj
  dsimp [state10]
  have h_iff : j < b - (k + 1) ↔ j + 1 < b - k := by omega
  simp only [h_iff]

/-- Step transition lemma: for every k < b, the transition from
    state10 b k to state10 b (k + 1) is valid in the chain SFT. -/
theorem state10_step_valid (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (k : ℕ) (hk : k < b) :
    isTransition a b ha hab (state10 b k) (state10 b (k + 1)) := by
  refine ⟨state10_shift b k hk, ?_⟩
  dsimp [validCons]
  have h_new : state10 b (k + 1) ⟨b - 1, by omega⟩ = false := by
    dsimp [state10]
    have : ¬ (b - 1 < b - (k + 1)) := by omega
    exact decide_eq_false this
  have h_old : state10 b k ⟨0, by omega⟩ = true := by
    dsimp [state10]
    have : 0 < b - k := by omega
    exact decide_eq_true this
  rw [h_new, h_old]
  exact validCons_zero_any_one (state10 b k ⟨b - a, by omega⟩)

/-- Multi-step reachability relation in the chain SFT. -/
inductive Reachable (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) : State b → State b → Prop where
  | refl (u : State b) : Reachable a b ha hab u u
  | step {u v w : State b} : Reachable a b ha hab u v → isTransition a b ha hab v w →
      Reachable a b ha hab u w

theorem Reachable.trans {a b : ℕ} {ha : 1 ≤ a} {hab : a < b} {u v w : State b}
    (h1 : Reachable a b ha hab u v) (h2 : Reachable a b ha hab v w) :
    Reachable a b ha hab u w := by
  induction h2 generalizing u with
  | refl => exact h1
  | step _ hw ih => exact Reachable.step (ih h1) hw

/-- The reachability lemma from state01 b 0 to state01 b k by induction. -/
theorem reachable_state01 (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (k : ℕ) (hk : k ≤ b) :
    Reachable a b ha hab (state01 b 0) (state01 b k) := by
  induction k with
  | zero => exact Reachable.refl _
  | succ m ih =>
    have hm : m < b := by omega
    have h_rec := ih (by omega)
    have h_step := state01_step_valid a b ha hab m hm
    exact Reachable.step h_rec h_step

/-- Master Reachability Theorem: 0ᵇ reaches 1ᵇ in the chain SFT. -/
theorem reachable_zero_to_one (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    Reachable a b ha hab (allZeros b) (allOnes b) := by
  rw [← state01_zero b, ← state01_self b]
  exact reachable_state01 a b ha hab b (le_refl b)

/-- The reachability lemma from state10 b 0 to state10 b k by induction. -/
theorem reachable_state10 (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (k : ℕ) (hk : k ≤ b) :
    Reachable a b ha hab (state10 b 0) (state10 b k) := by
  induction k with
  | zero => exact Reachable.refl _
  | succ m ih =>
    have hm : m < b := by omega
    have h_rec := ih (by omega)
    have h_step := state10_step_valid a b ha hab m hm
    exact Reachable.step h_rec h_step

/-- Master Reachability Theorem: 1ᵇ reaches 0ᵇ in the chain SFT. -/
theorem reachable_one_to_zero (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    Reachable a b ha hab (allOnes b) (allZeros b) := by
  rw [← state10_zero b, ← state10_self b]
  exact reachable_state10 a b ha hab b (le_refl b)

/-- Two states u and v are in the same Strongly Connected Component (SCC). -/
def InSameSCC (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (u v : State b) : Prop :=
  Reachable a b ha hab u v ∧ Reachable a b ha hab v u

/-- Component Equivalence Theorem:
    The all-zero state 0ᵇ and the all-one state 1ᵇ belong to the
    EXACT SAME Strongly Connected Component of the chain SFT. -/
theorem zero_and_one_in_same_scc (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    InSameSCC a b ha hab (allZeros b) (allOnes b) :=
  ⟨reachable_zero_to_one a b ha hab, reachable_one_to_zero a b ha hab⟩

/-- Primitive Component Theorem:
    Because 0ᵇ has a self-loop (a cycle of length 1) and is mutually reachable with 1ᵇ,
    the recurrent component containing 0ᵇ and 1ᵇ is aperiodic (period = 1). -/
theorem recurrent_component_has_period_one (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    isTransition a b ha hab (allZeros b) (allZeros b) ∧
    InSameSCC a b ha hab (allZeros b) (allOnes b) :=
  ⟨allZeros_self_loop a b ha hab, zero_and_one_in_same_scc a b ha hab⟩

/-- Cancellation lemma: if the oldest bit is the negation of the newly appended bit,
    the ternary constraint validCons x y (! x) = true holds identically for all booleans x, y. -/
theorem validCons_not_cancel (x y : Bool) : validCons x y (! x) = true := by
  cases x <;> cases y <;> decide

/-- The universal alternating 2b-periodic sequence on ℤ:
    z i = true iff (i mod 2b) ≥ b. -/
def periodicSeq (b : ℕ) (i : ℤ) : Bool :=
  decide ((i % (2 * (b : ℤ))) ≥ (b : ℤ))

theorem mod_neg_plus (m x : ℤ) (h1 : 0 ≤ x) (h2 : x < m) :
    (-1 * m + x) % m = x := by
  have : -1 * m + x = x + m * (-1) := by ring
  rw [this, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt h1 h2

/-- Shifting by b inverts the bit value: z_{i-b} = ¬ z_i for all i ∈ ℤ. -/
theorem periodicSeq_shift_b (b : ℕ) (hb : 1 ≤ b) (i : ℤ) :
    periodicSeq b (i - (b : ℤ)) = ! (periodicSeq b i) := by
  dsimp [periodicSeq]
  have hb2 : (0 : ℤ) < 2 * (b : ℤ) := by omega
  have hb_pos : (0 : ℤ) ≤ (b : ℤ) := by omega
  have hb_lt : (b : ℤ) < 2 * (b : ℤ) := by omega
  have hb_mod : (b : ℤ) % (2 * (b : ℤ)) = (b : ℤ) := Int.emod_eq_of_lt hb_pos hb_lt
  have h_sub_mod : (i - (b : ℤ)) % (2 * (b : ℤ)) = (i % (2 * (b : ℤ)) - (b : ℤ)) % (2 * (b : ℤ)) := by
    have h := Int.sub_emod i (b : ℤ) (2 * (b : ℤ))
    rw [hb_mod] at h
    exact h
  set r := i % (2 * (b : ℤ))
  have _hmod : 0 ≤ r := Int.emod_nonneg i (by omega)
  have _hlt : r < 2 * (b : ℤ) := Int.emod_lt_of_pos i hb2
  rw [h_sub_mod]
  by_cases hr : r < (b : ℤ)
  · have hr_sub : (r - (b : ℤ)) % (2 * (b : ℤ)) = r + (b : ℤ) := by
      have h_alg : r - (b : ℤ) = -1 * (2 * (b : ℤ)) + (r + (b : ℤ)) := by ring
      rw [h_alg]
      apply mod_neg_plus
      · omega
      · omega
    rw [hr_sub]
    have h_ge : decide (r + (b : ℤ) ≥ (b : ℤ)) = true := by
      apply decide_eq_true
      omega
    have h_lt : decide (r ≥ (b : ℤ)) = false := by
      apply decide_eq_false
      omega
    rw [h_ge, h_lt]
    rfl
  · have hr_sub : (r - (b : ℤ)) % (2 * (b : ℤ)) = r - (b : ℤ) := by
      have h1 : 0 ≤ r - (b : ℤ) := by omega
      have h2 : r - (b : ℤ) < 2 * (b : ℤ) := by omega
      exact Int.emod_eq_of_lt h1 h2
    rw [hr_sub]
    have h_lt : decide (r - (b : ℤ) ≥ (b : ℤ)) = false := by
      apply decide_eq_false
      omega
    have h_ge : decide (r ≥ (b : ℤ)) = true := by
      apply decide_eq_true
      omega
    rw [h_lt, h_ge]
    rfl

/-- Universal Admissibility Theorem:
    The alternating 2b-periodic sequence satisfies the chain SFT constraint
    identically at every position i ∈ ℤ for all parameters 1 ≤ a < b. -/
theorem periodicSeq_constraint (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (i : ℤ) :
    validCons (periodicSeq b i) (periodicSeq b (i - (a : ℤ))) (periodicSeq b (i - (b : ℤ))) = true := by
  have hb : 1 ≤ b := by omega
  rw [periodicSeq_shift_b b hb i]
  exact validCons_not_cancel (periodicSeq b i) (periodicSeq b (i - (a : ℤ)))

/-- Witness 1 Occurrence Theorem (g = 1):
    For any b ≥ 1, the non-extremizer witness word 0^b 1 occurs as an exact
    contiguous subword of the universal alternating periodic sequence at indices 0 .. b. -/
theorem witness_g_eq_1_occurs (b : ℕ) (hb : 1 ≤ b) :
    (∀ i : ℕ, i < b → periodicSeq b (i : ℤ) = false) ∧
    periodicSeq b (b : ℤ) = true := by
  constructor
  · intro i hi
    dsimp [periodicSeq]
    have h1 : (0 : ℤ) ≤ (i : ℤ) := by omega
    have h2 : (i : ℤ) < 2 * (b : ℤ) := by omega
    have hmod : (i : ℤ) % (2 * (b : ℤ)) = (i : ℤ) := Int.emod_eq_of_lt h1 h2
    rw [hmod]
    apply decide_eq_false
    omega
  · dsimp [periodicSeq]
    have h1 : (0 : ℤ) ≤ (b : ℤ) := by omega
    have h2 : (b : ℤ) < 2 * (b : ℤ) := by omega
    have hmod : (b : ℤ) % (2 * (b : ℤ)) = (b : ℤ) := Int.emod_eq_of_lt h1 h2
    rw [hmod]
    apply decide_eq_true
    omega

/-- Witness 2 Occurrence Theorem (g ≥ 2):
    For any b ≥ 2, the non-extremizer witness word 0^{b-1} 1 1 occurs as an exact
    contiguous subword of the universal alternating periodic sequence at indices 1 .. b + 1. -/
theorem witness_g_ge_2_occurs (b : ℕ) (hb : 2 ≤ b) :
    (∀ i : ℕ, 1 ≤ i ∧ i < b → periodicSeq b (i : ℤ) = false) ∧
    periodicSeq b (b : ℤ) = true ∧
    periodicSeq b ((b + 1 : ℕ) : ℤ) = true := by
  have hw1 := witness_g_eq_1_occurs b (by omega)
  refine ⟨fun i hi => hw1.1 i hi.2, hw1.2, ?_⟩
  dsimp [periodicSeq]
  have h1 : (0 : ℤ) ≤ ((b + 1 : ℕ) : ℤ) := by omega
  have h2 : ((b + 1 : ℕ) : ℤ) < 2 * (b : ℤ) := by omega
  have hmod : ((b + 1 : ℕ) : ℤ) % (2 * (b : ℤ)) = ((b + 1 : ℕ) : ℤ) := Int.emod_eq_of_lt h1 h2
  rw [hmod]
  apply decide_eq_true
  omega

end ErdosTernary.PeriodicOrbit
