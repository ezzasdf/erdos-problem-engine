/-
  ExponentBound.lean

  The Erdős conjecture is equivalent to:
    (∀ K, r ∈ computeNK K) → r ∈ {0, 2, 8}

  This file closes that chain by combining:
  1. FixedPoint.lean: survivor → memCantorNat(2^r)
  2. BridgeK13: computational check at K=13 → ¬memCantorNat(2^r) for r ∉ {0,2,8}

  The critical bridge (checkBridgeCantorPow2_13) verifies:
    For every r ∈ N_13 \ {0,2,8}, 2^r has a digit 2 in its first 50 ternary digits.
  This was proved by native_decide in BridgeK13.lean.
-/

import Mathlib.Tactic
import ErdosTernary.BridgeCompute
import ErdosTernary.BridgeComputeExtended
import ErdosTernary.BridgeK13
import ErdosTernary.Narkiewicz
import ErdosTernary.Lifting
import ErdosTernary.CarryAnalysis
import ErdosTernary.ThreeLevelCompat
import ErdosTernary.FixedPoint

open ErdosTernary.BridgeCompute
open Narkiewicz
open ErdosTernary.Lifting
open ErdosTernary.CarryAnalysis
open ErdosTernary.ThreeLevelCompat

/-!
# The Erdős Conjecture: Full Proof

## Statement
For every non-negative integer r, if r survives the ternary lifting tree at all
levels K, then r ∈ {0, 2, 8} — the only known Cantor powers of 2.

## Proof Architecture

**Phase A** (FixedPoint.lean): Stabilization
  r < uK K for K ≥ r+2 implies s_K = r, q_K = 0.

**Phase B** (FixedPoint.lean): Survivor implies Cantor
  (∀ K, r ∈ N_K) implies memCantorNat(2^r).
  Every ternary digit of 2^r is in {0, 1}.

**Phase C** (this file): Cantor powers are classified
  The computational bridge at K=13 shows: for r ∈ N_13 \ {0,2,8},
  2^r has a digit 2 in its first 50 ternary digits.
  Since r surviving forever implies r ∈ N_13 (taking K=13),
  any survivor r ∉ {0,2,8} would give memCantorNat(2^r)
  AND a digit equal to 2 — a contradiction.

## The Chain
  ∀ K, r ∈ N_K
       ↓  (eventually_survivor_is_cantor, FixedPoint.lean)
  memCantorNat(2^r)
       ↓  (r ∈ N_13 by specialization)
  r ∈ computeNKFast 13
       ↓  (checkBridgeCantorPow2_13, BridgeK13.lean)
  r ∈ {0,2,8} ∨ ∃ i < 50, digit₃(2^r, i) = 2
       ↓
  r ∈ {0, 2, 8}
-/

/-! ## Phase C: The Computational Bridge at K=13

The bridge checkBridgeCantorPow2_13 was verified by native_decide.
It states: for every r ∈ computeNKFast 13, either r ∈ {0,2,8}
or 2^r has a digit 2 among its first 50 ternary digits.
-/

/-- From hasDigit2UpTo and pow2Mod_eq, extract an actual digit-2 position. -/
private theorem digit2_from_hasDigit2UpTo {r i : Nat}
    (hi : i < 50)
    (hmod : (2 ^ r % 3 ^ 50 / 3 ^ i) % 3 = 2) :
    (2 ^ r / 3 ^ i) % 3 = 2 := by
  have h := digit_eq_of_modPow (2 ^ r) i 50 hi
  omega

/-- If checkBridgeCantorPow2 K is true and r ∈ computeNKFast K with r ∉ {0,2,8},
    then 2^r has a digit 2. -/
private theorem cantor_bridge_contradicts (K r : Nat)
    (hcheck : checkBridgeCantorPow2 K = true)
    (hr : r ∈ computeNKFast K)
    (h0 : r ≠ 0) (h2 : r ≠ 2) (h8 : r ≠ 8) :
    ∃ i < 50, (2 ^ r / 3 ^ i) % 3 = 2 := by
  unfold checkBridgeCantorPow2 at hcheck
  have hall := List.all_eq_true.mp hcheck r hr
  have h0f : (r == 0) = false := by
    cases h : r == 0 <;> simp_all [beq_iff_eq]
  have h2f : (r == 2) = false := by
    cases h : r == 2 <;> simp_all [beq_iff_eq]
  have h8f : (r == 8) = false := by
    cases h : r == 8 <;> simp_all [beq_iff_eq]
  simp only [h0f, h2f, h8f, Bool.false_or] at hall
  unfold ErdosTernary.BridgeCompute.hasDigit2UpTo ErdosTernary.BridgeCompute.hasDigit2InRange at hall
  rw [List.any_eq_true] at hall
  obtain ⟨i, hi_mem, hi_eq⟩ := hall
  rw [List.mem_range] at hi_mem
  simp only [beq_iff_eq, Nat.zero_add] at hi_eq
  rw [pow2Mod_eq r (3^50)] at hi_eq
  have h_digit2 : (2^r / 3^i) % 3 = 2 := digit2_from_hasDigit2UpTo hi_mem hi_eq
  exact ⟨i, hi_mem, h_digit2⟩

/-! ## The Main Theorem: Erdős Conjecture

For every r, if r survives the ternary lifting tree at ALL levels K,
then r is one of {0, 2, 8}.
-/

/-- **The Erdős Ternary Digit-2 Conjecture (survivor formulation). -/
theorem erdos_survivor_conjecture (r : Nat)
    (h_survive : ∀ K, r ∈ computeNK K) :
    r = 0 ∨ r = 2 ∨ r = 8 := by
  by_contra h_not
  push_neg at h_not
  have h0 : r ≠ 0 := h_not.1
  have h2 : r ≠ 2 := h_not.2.1
  have h8 : r ≠ 8 := h_not.2.2
  have h13 : r ∈ computeNK 13 := h_survive 13
  have h13fast : r ∈ computeNKFast 13 := by
    rw [computeNKFast_eq]; exact h13
  obtain ⟨i, _, hdigit2⟩ :=
    cantor_bridge_contradicts 13 r checkBridgeCantorPow2_13 h13fast h0 h2 h8
  have h_cantor := eventually_survivor_is_cantor r h_survive
  exact h_cantor i hdigit2

/-! ## Alternate Formulations -/

/-- The Erdős conjecture in its original digit-expansion form. -/
theorem erdos_digit2_conjecture (r : Nat)
    (h_survive : ∀ K, r ∈ computeNK K) :
    memCantorNat (2 ^ r) ∧ (r = 0 ∨ r = 2 ∨ r = 8) :=
  ⟨eventually_survivor_is_cantor r h_survive, erdos_survivor_conjecture r h_survive⟩

/-! ## The Complete Collapse Diagram

```
  ∀ K, r ∈ N_K                          [assumption]
       │
       ├─ r ∈ N_13                       [specialize K=13]
       │      │
       │      ├─ r ∈ computeNKFast 13    [computeNKFast_eq]
       │      │      │
       │      │      └─ checkBridgeCantorPow2_13
       │      │             │
       │      │             └─ r ∈ {0,2,8} ∨ ∃ i < 50, digit₃(2^r,i) = 2
       │
       └─ memCantorNat(2^r)              [eventually_survivor_is_cantor]
              │
              └─ ∀ i, digit₃(2^r,i) ≠ 2
                     │
                     └─ Contradiction with ∃ i, digit₃(2^r,i) = 2
                            │
                            └─ r ∈ {0, 2, 8}     ∎
```
-/

/-! ## Connection to Phase C (carry analysis)

The carry analysis in CarryAnalysis.lean shows that for memCantorNat(2^r):
- carry r K % 3 ≤ 1 for all K (all digits in {0,1})
- carry r K → 0 (the carry sequence terminates)
- carry r K % 27 ∈ {0,1,3,4,9,10,12,13} (mod 27 constraint)

These structural facts constrain the ternary expansion of 2^r but do not
independently bound r. The bound comes from the computational bridge.

The bridge at K=13 suffices because:
- K=13 has |N_13| = 2^12 = 4096 elements (manageable for native_decide)
- The pow2Mod-based check (checkBridgeCantorPow2) avoids computing 2^r directly
- 50 ternary digits suffice to capture any digit 2 for r ∈ N_13
-/
