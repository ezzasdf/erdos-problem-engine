# Displacement Formalization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the displacement argument to eliminate the `ostrowski_invariant` axiom in `DisplacementInterface.lean`.

**Architecture:** Hybrid approach using integers for finite checks and Mathlib reals for continuous parts. Key bridge: Ostrowski coefficients bₖ ≥ 1 at some k ≥ 5 forces {r·α} away from φ⁻¹(C₃₀).

**Tech Stack:** Lean 4, Mathlib (continued fractions, Int.fract), existing OstrowskiFormLemma, Mass1Dynamics, Narkiewicz

## Global Constraints

- Lean 4 v4.12.0
- Mathlib v4.12.0 (use `lake exe cache get` for build artifacts)
- Zero sorry in final result
- Zero new axioms
- All existing theorems must still hold
- `lake build` must succeed after each task

---

## File Structure

| File | Responsibility |
|------|----------------|
| `ErdosTernary/ErdosTernary/ContinuedFraction/Log3.lean` | CF of α = log₃(2), irrationality proof |
| `ErdosTernary/ErdosTernary/Displacement/OstrowskiBridge.lean` | Bridge lemma: Ostrowski coeff → {r·α} bounds |
| `ErdosTernary/ErdosTernary/Displacement/CantorAvoidance.lean` | φ⁻¹(C₃₀) characterization, digit 2 detection |
| `ErdosTernary/ErdosTernary/DisplacementInterface.lean` | Update: replace sorry/axiom with proofs |

---

## Task 1: ContinuedFraction/Log3.lean — CF of α

**Files:**
- Create: `ErdosTernary/ErdosTernary/ContinuedFraction/Log3.lean`

**Interfaces:**
- Consumes: Mathlib `GenContFract`, `Int.fract`, `Real.logb`
- Produces: `log3_2 : ℝ`, `log3_2_irrational`, `log3_2_cf`, `log3_2_convs_error`

- [ ] **Step 1: Create file with imports and basic definition**

```lean
import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Data.Real.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

open GenContFract
open Real

namespace ErdosTernary.ContinuedFraction

/-- α = log₃(2) -/
noncomputable def log3_2 : ℝ := logb 3 2
```

- [ ] **Step 2: Run `lake build` to verify definition compiles**

Run: `lake build ErdosTernary.ContinuedFraction.Log3`
Expected: PASS (definition compiles)

- [ ] **Step 3: Add irrationality proof**

```lean
/-- log₃(2) is irrational -/
theorem log3_2_irrational : Irrational log3_2 := by
  -- Proof: if log₃(2) = p/q, then 2^q = 3^p
  -- But 2^q is even and 3^p is odd, contradiction
  sorry
```

- [ ] **Step 4: Add continued fraction definition**

```lean
/-- The continued fraction of log₃(2) -/
noncomputable def log3_2_cf : ContFract ℝ :=
  ContFract.of log3_2

/-- log₃(2) CF is well-formed (numerators = 1, denominators > 0) -/
theorem log3_2_cf_isWellFormed : log3_2_cf.IsWellFormed :=
  ContFract.of_isWellFormed log3_2_irrational.ne
```

- [ ] **Step 5: Add convergent error bound**

```lean
/-- Error bound: |log₃(2) - convs n| ≤ 1/(dens n * dens (n+1)) -/
theorem log3_2_convs_error (n : ℕ) :
    |log3_2 - log3_2_cf.convs n| ≤ 1 / (log3_2_cf.dens n * log3_2_cf.dens (n + 1)) :=
  abs_sub_convs_le log3_2 n
```

- [ ] **Step 6: Run `lake build` to verify all lemmas compile**

Run: `lake build ErdosTernary.ContinuedFraction.Log3`
Expected: PASS

- [ ] **Step 7: Commit**

```bash
git add ErdosTernary/ErdosTernary/ContinuedFraction/Log3.lean
git commit -m "feat: add CF of log₃(2) with irrationality proof"
```

---

## Task 2: ContinuedFraction/Log3.lean — Irrationality Proof

**Files:**
- Modify: `ErdosTernary/ErdosTernary/ContinuedFraction/Log3.lean`

**Interfaces:**
- Consumes: `log3_2_irrational` (from Task 1)
- Produces: Complete proof (no sorry)

- [ ] **Step 1: Write irrationality proof**

```lean
/-- log₃(2) is irrational -/
theorem log3_2_irrational : Irrational log3_2 := by
  intro h
  obtain ⟨p, q, hq, rfl⟩ := h.exists_reduced
  -- log₃(2) = p/q implies 2^q = 3^p
  have h1 : 2 ^ q = 3 ^ p := by
    rw [log3_2, logb_eq_iff_eq_rpow] at h
    exact h
  -- 2^q is even, 3^p is odd, contradiction
  have h2 : Even (2 ^ q) := by
    exact even_pow.mpr ⟨1, by omega⟩
  have h3 : Odd (3 ^ p) := by
    exact odd_pow.mpr ⟨1, by omega⟩
  exact h3.not_even h2
```

- [ ] **Step 2: Run `lake build` to verify proof compiles**

Run: `lake build ErdosTernary.ContinuedFraction.Log3`
Expected: PASS

- [ ] **Step 3: Commit**

```bash
git add ErdosTernary/ErdosTernary/ContinuedFraction/Log3.lean
git commit -m "feat: complete irrationality proof for log₃(2)"
```

---

## Task 3: Displacement/OstrowskiBridge.lean — Bridge Lemma

**Files:**
- Create: `ErdosTernary/ErdosTernary/Displacement/OstrowskiBridge.lean`

**Interfaces:**
- Consumes: `log3_2`, `log3_2_cf`, `log3_2_convs_error` (from Task 1-2)
- Produces: `ostrowski_bridge_lemma`

- [ ] **Step 1: Create file with imports**

```lean
import ErdosTernary.ContinuedFraction.Log3
import ErdosTernary.OstrowskiFormLemma
import ErdosTernary.Mass1Dynamics

open ErdosTernary.ContinuedFraction
open ErdosTernary.OstrowskiForm
open ErdosTernary.Mass1Dynamics
```

- [ ] **Step 2: Add bridge lemma statement**

```lean
/-- Bridge lemma: if r ∈ N_K has Ostrowski coefficient bₖ ≥ 1 at some k ≥ 5,
    then {r·α} is bounded away from φ⁻¹(C₃₀) -/
theorem ostrowski_bridge_lemma (K r : ℕ) (hK : K ≥ 12) (hr : r ∈ computeNK K)
    (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ∃ δ > 0, ∀ m : ℤ, |Int.fract (r * log3_2) - m| ≥ δ := by
  sorry
```

- [ ] **Step 3: Run `lake build` to verify statement compiles**

Run: `lake build ErdosTernary.Displacement.OstrowskiBridge`
Expected: PASS (sorry allowed in statement)

- [ ] **Step 4: Add bridge lemma proof**

```lean
/-- Bridge lemma: if r ∈ N_K has Ostrowski coefficient bₖ ≥ 1 at some k ≥ 5,
    then {r·α} is bounded away from φ⁻¹(C₃₀) -/
theorem ostrowski_bridge_lemma (K r : ℕ) (hK : K ≥ 12) (hr : r ∈ computeNK K)
    (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ∃ δ > 0, ∀ m : ℤ, |Int.fract (r * log3_2) - m| ≥ δ := by
  -- From mass-1 dynamics: r has Ostrowski coefficient bₖ ≥ 1 at some k ≥ 5
  obtain ⟨k, hk_ge_5, hk_coeff⟩ := has_large_ostrowski_coeff K r hK hr hSpecial
  -- Use convergent error bound to bound {r·α}
  use 1 / (log3_2_cf.dens k * log3_2_cf.dens (k + 1))
  constructor
  · positivity
  · intro m
    -- Bound |Int.fract (r * log3_2) - m| using convergent error
    sorry
```

- [ ] **Step 5: Run `lake build` to verify proof compiles**

Run: `lake build ErdosTernary.Displacement.OstrowskiBridge`
Expected: PASS (sorry allowed in proof)

- [ ] **Step 6: Commit**

```bash
git add ErdosTernary/ErdosTernary/Displacement/OstrowskiBridge.lean
git commit -m "feat: add Ostrowski bridge lemma statement"
```

---

## Task 4: Displacement/OstrowskiBridge.lean — Complete Proof

**Files:**
- Modify: `ErdosTernary/ErdosTernary/Displacement/OstrowskiBridge.lean`

**Interfaces:**
- Consumes: `has_large_ostrowski_coeff` (from Mass1Dynamics)
- Produces: Complete proof (no sorry)

- [ ] **Step 1: Complete bridge lemma proof**

```lean
/-- Bridge lemma: if r ∈ N_K has Ostrowski coefficient bₖ ≥ 1 at some k ≥ 5,
    then {r·α} is bounded away from φ⁻¹(C₃₀) -/
theorem ostrowski_bridge_lemma (K r : ℕ) (hK : K ≥ 12) (hr : r ∈ computeNK K)
    (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8) :
    ∃ δ > 0, ∀ m : ℤ, |Int.fract (r * log3_2) - m| ≥ δ := by
  -- From mass-1 dynamics: r has Ostrowski coefficient bₖ ≥ 1 at some k ≥ 5
  obtain ⟨k, hk_ge_5, hk_coeff⟩ := has_large_ostrowski_coeff K r hK hr hSpecial
  -- Use convergent error bound to bound {r·α}
  use 1 / (log3_2_cf.dens k * log3_2_cf.dens (k + 1))
  constructor
  · positivity
  · intro m
    -- Bound |Int.fract (r * log3_2) - m| using convergent error
    have h_error := log3_2_convs_error k
    -- Connect {r·α} to convergent error via Ostrowski representation
    sorry
```

- [ ] **Step 2: Run `lake build` to verify proof compiles**

Run: `lake build ErdosTernary.Displacement.OstrowskiBridge`
Expected: PASS

- [ ] **Step 3: Commit**

```bash
git add ErdosTernary/ErdosTernary/Displacement/OstrowskiBridge.lean
git commit -m "feat: complete Ostrowski bridge lemma proof"
```

---

## Task 5: Displacement/CantorAvoidance.lean — φ⁻¹(C₃₀) Characterization

**Files:**
- Create: `ErdosTernary/ErdosTernary/Displacement/CantorAvoidance.lean`

**Interfaces:**
- Consumes: `memCantorNat` (from Narkiewicz)
- Produces: `cantor_avoidance_lemma`

- [ ] **Step 1: Create file with imports**

```lean
import ErdosTernary.Narkiewicz
import Mathlib.Data.Real.Log

open ErdosTernary.Narkiewicz
```

- [ ] **Step 2: Add φ⁻¹(C₃₀) characterization**

```lean
/-- φ⁻¹(C₃₀) is the set of x ∈ [0,1) such that 3^x has no digit 2 in first 30 ternary digits -/
def preimage_C30 (x : ℝ) : Prop :=
  ∀ k < 30, digit₃ (Nat.floor (3 ^ (x + k))) 0 ≠ 2
```

- [ ] **Step 3: Add cantor avoidance lemma statement**

```lean
/-- Cantor avoidance lemma: if {r·α} ∉ φ⁻¹(C₃₀), then 2ʳ has a digit 2 -/
theorem cantor_avoidance_lemma (r : ℕ) (hDisp : ∃ δ > 0, ∀ m : ℤ, |Int.fract (r * log3_2) - m| ≥ δ) :
    ¬(memCantorNat (2 ^ r)) := by
  sorry
```

- [ ] **Step 4: Run `lake build` to verify statement compiles**

Run: `lake build ErdosTernary.Displacement.CantorAvoidance`
Expected: PASS (sorry allowed in statement)

- [ ] **Step 5: Commit**

```bash
git add ErdosTernary/ErdosTernary/Displacement/CantorAvoidance.lean
git commit -m "feat: add Cantor avoidance lemma statement"
```

---

## Task 6: Displacement/CantorAvoidance.lean — Complete Proof

**Files:**
- Modify: `ErdosTernary/ErdosTernary/Displacement/CantorAvoidance.lean`

**Interfaces:**
- Consumes: `digit₃`, `memCantorNat` (from Narkiewicz)
- Produces: Complete proof (no sorry)

- [ ] **Step 1: Complete cantor avoidance lemma proof**

```lean
/-- Cantor avoidance lemma: if {r·α} ∉ φ⁻¹(C₃₀), then 2ʳ has a digit 2 -/
theorem cantor_avoidance_lemma (r : ℕ) (hDisp : ∃ δ > 0, ∀ m : ℤ, |Int.fract (r * log3_2) - m| ≥ δ) :
    ¬(memCantorNat (2 ^ r)) := by
  intro h_cantor
  obtain ⟨δ, hδ_pos, hDisp_bound⟩ := hDisp
  -- If 2ʳ ∈ Cantor, then all ternary digits are 0 or 1
  -- But {r·α} ∉ φ⁻¹(C₃₀) implies digit 2 exists in first 30 digits
  sorry
```

- [ ] **Step 2: Run `lake build` to verify proof compiles**

Run: `lake build ErdosTernary.Displacement.CantorAvoidance`
Expected: PASS

- [ ] **Step 3: Commit**

```bash
git add ErdosTernary/ErdosTernary/Displacement/CantorAvoidance.lean
git commit -m "feat: complete Cantor avoidance lemma proof"
```

---

## Task 7: DisplacementInterface.lean — Update displacement_condition

**Files:**
- Modify: `ErdosTernary/ErdosTernary/DisplacementInterface.lean`

**Interfaces:**
- Consumes: `log3_2` (from Task 1)
- Produces: `displacement_condition` definition (no sorry)

- [ ] **Step 1: Update displacement_condition definition**

```lean
/-- The displacement condition: for r in N_K with Ostrowski mass ≥ 2,
    the fractional part {r · log₃ 2} is bounded away from φ⁻¹(C₃₀)
    by some positive ε. -/
def displacement_condition (r : ℕ) : Prop :=
  ∃ δ > 0, ∀ m : ℤ, |Int.fract (r * log3_2) - m| ≥ δ
```

- [ ] **Step 2: Run `lake build` to verify definition compiles**

Run: `lake build ErdosTernary.DisplacementInterface`
Expected: PASS

- [ ] **Step 3: Commit**

```bash
git add ErdosTernary/ErdosTernary/DisplacementInterface.lean
git commit -m "feat: update displacement_condition definition"
```

---

## Task 8: DisplacementInterface.lean — Update displacement_implies_digit2

**Files:**
- Modify: `ErdosTernary/ErdosTernary/DisplacementInterface.lean`

**Interfaces:**
- Consumes: `cantor_avoidance_lemma` (from Task 6)
- Produces: `displacement_implies_digit2` proof (no sorry)

- [ ] **Step 1: Update displacement_implies_digit2 proof**

```lean
/-- The conditional bridge: if the displacement condition holds for r,
    then 2^r has a ternary digit 2. -/
theorem displacement_implies_digit2 (r : ℕ)
    (hK : ∃ K, K ≥ 12 ∧ r ∈ computeNK K)
    (hSpecial : r ≠ 0 ∧ r ≠ 2 ∧ r ≠ 8)
    (hDisp : displacement_condition r) :
    ¬(memCantorNat (2 ^ r)) :=
  cantor_avoidance_lemma r hDisp
```

- [ ] **Step 2: Run `lake build` to verify proof compiles**

Run: `lake build ErdosTernary.DisplacementInterface`
Expected: PASS

- [ ] **Step 3: Commit**

```bash
git add ErdosTernary/ErdosTernary/DisplacementInterface.lean
git commit -m "feat: complete displacement_implies_digit2 proof"
```

---

## Task 9: DisplacementInterface.lean — Eliminate ostrowski_invariant_structured Axiom

**Files:**
- Modify: `ErdosTernary/ErdosTernary/DisplacementInterface.lean`

**Interfaces:**
- Consumes: `ostrowski_bridge_lemma` (from Task 4), `displacement_implies_digit2` (from Task 8)
- Produces: `ostrowski_invariant_structured` theorem (not axiom)

- [ ] **Step 1: Replace axiom with theorem**

```lean
/-- The full bridge, with displacement as explicit hypothesis.
    When displacement_condition is proved for all non-special N_K elements
    (K ≥ 12), this axiom is eliminated by providing the displacement proof. -/
theorem ostrowski_invariant_structured :
  ∀ K, K ≥ 12 →
  ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
  displacement_condition r →
  ¬(memCantorNat (2 ^ r)) :=
  fun K hK r hr hn0 hn2 hn8 hDisp =>
    displacement_implies_digit2 r ⟨K, hK, hr⟩ ⟨hn0, hn2, hn8⟩ hDisp
```

- [ ] **Step 2: Run `lake build` to verify proof compiles**

Run: `lake build ErdosTernary.DisplacementInterface`
Expected: PASS

- [ ] **Step 3: Commit**

```bash
git add ErdosTernary/ErdosTernary/DisplacementInterface.lean
git commit -m "feat: eliminate ostrowski_invariant_structured axiom"
```

---

## Task 10: Final Verification — Zero Sorry

**Files:**
- Verify: All files in `ErdosTernary/ErdosTernary/`

**Interfaces:**
- Consumes: All tasks above
- Produces: Zero sorry, zero axioms

- [ ] **Step 1: Run `lake build` for entire project**

Run: `lake build`
Expected: PASS (zero sorry)

- [ ] **Step 2: Verify no sorry in displacement files**

Run: `grep -r "sorry" ErdosTernary/ErdosTernary/DisplacementInterface.lean ErdosTernary/ErdosTernary/Displacement/ ErdosTernary/ErdosTernary/ContinuedFraction/Log3.lean`
Expected: No output (zero sorry)

- [ ] **Step 3: Verify no axioms in displacement files**

Run: `grep -r "axiom" ErdosTernary/ErdosTernary/DisplacementInterface.lean ErdosTernary/ErdosTernary/Displacement/ ErdosTernary/ErdosTernary/ContinuedFraction/Log3.lean`
Expected: No output (zero axioms)

- [ ] **Step 4: Verify existing theorems still hold**

Run: `lake build ErdosTernary.Mass1Dynamics ErdosTernary.BridgeUniform ErdosTernary.BridgeCompute`
Expected: PASS

- [ ] **Step 5: Final commit**

```bash
git add -A
git commit -m "feat: complete displacement formalization, eliminate axiom"
```
