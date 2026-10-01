# Displacement Formalization Design

**Date:** 2026-08-31
**Status:** APPROVED
**Approach:** Hybrid (Integer + Mathlib Real)

## Overview

Formalize the displacement argument to eliminate the `ostrowski_invariant` axiom in `DisplacementInterface.lean`. The displacement condition connects Ostrowski mass to Cantor set avoidance via Diophantine approximation.

## Architecture

```
Ostrowski World          Real World           Ternary World
(discrete)               (continuous)         (digit-based)
                                                
N_K membership     →    {r · α} bounds   →   Cantor set C₃₀
Ostrowski coeffs   →    CF convergents    →   φ⁻¹(C₃₀)
digit extraction   →    fractional parts  →   digit 2 presence
```

**Key bridge lemma:** For r ∈ N_K \ {0,2,8}, the Ostrowski representation forces {r·α} away from φ⁻¹(C₃₀).

## Components

### Component 1: ContinuedFraction/Log3.lean
- Defines α = log₃(2) as a real number
- Computes its continued fraction expansion using Mathlib's `GenContFract.of`
- Proves α is irrational (needed for infinite CF)
- Extracts convergent denominators qₖ and error bounds

### Component 2: Displacement/OstrowskiBridge.lean
- Key bridge: if r ∈ N_K has Ostrowski coefficient bₖ ≥ 1 at some k ≥ 5, then {r·α} is bounded away from φ⁻¹(C₃₀)
- Uses convergent error bounds: |α - pₖ/qₖ| ≤ 1/(qₖ·qₖ₊₁)
- Proves the displacement condition for all non-special N_K elements

### Component 3: Displacement/CantorAvoidance.lean
- Characterizes φ⁻¹(C₃₀) in terms of fractional parts
- Proves: if {r·α} is bounded away from φ⁻¹(C₃₀) by some ε > 0, then 2ʳ has a digit 2
- Connects to existing `memCantorNat` definition

### Component 4: DisplacementInterface.lean (update)
- Replaces `displacement_condition` sorry with actual definition
- Replaces `displacement_implies_digit2` sorry with proof
- Eliminates `ostrowski_invariant_structured` axiom

## Data Flow

### Flow for proving `displacement_condition r`:

```
Input: r ∈ N_K (K ≥ 12)
        ↓
Step 1: Compute Ostrowski coefficients of r
        bₖ(r) for k = 0, 1, 2, ...
        ↓
Step 2: Find k ≥ 5 where bₖ(r) ≥ 1
        (exists by `no_mass1_for_large_K` + mass-1 dynamics)
        ↓
Step 3: Use convergent error bound
        |α - pₖ/qₖ| ≤ 1/(qₖ·qₖ₊₁)
        ↓
Step 4: Bound {r·α} away from φ⁻¹(C₃₀)
        {r·α} ∈ [δ, 1-δ] for some δ > 0
        ↓
Output: displacement_condition r holds
```

### Flow for proving `displacement_implies_digit2 r`:

```
Input: displacement_condition r
        ↓
Step 1: {r·α} ∉ φ⁻¹(C₃₀)
        ↓
Step 2: 3^{{r·α}} has digit 2 in first 30 ternary digits
        ↓
Step 3: 2ʳ has digit 2 in ternary representation
        ↓
Output: ¬(memCantorNat (2 ^ r))
```

## Sorry Elimination Strategy

### Current state in DisplacementInterface.lean:
- `displacement_condition`: defined as `sorry`
- `displacement_implies_digit2`: proof contains `sorry`
- `ostrowski_invariant_structured`: declared as `axiom`

### Elimination plan:

| Sorry/Axiom | Elimination Method | Difficulty |
|-------------|-------------------|------------|
| `displacement_condition` | Define using `{r·α}` bounds from CF convergents | Medium |
| `displacement_implies_digit2` | Prove using Cantor set characterization | Medium |
| `ostrowski_invariant_structured` | Prove using displacement_condition + existing theorems | Easy (logic) |

### Detailed elimination:

1. **`displacement_condition`**: Replace `sorry` with:
   ```lean
   def displacement_condition (r : ℕ) : Prop :=
     ∃ δ > 0, ∀ m : ℤ, |Int.fract (r * Real.logb 3 2) - m| ≥ δ
   ```
   This says {r·α} is bounded away from all integers by δ > 0.

2. **`displacement_implies_digit2`**: Prove using:
   - If {r·α} ∉ φ⁻¹(C₃₀), then 3^{{r·α}} has digit 2 in first 30 ternary digits
   - Therefore 2ʳ has digit 2 in ternary representation
   - Therefore ¬(memCantorNat (2 ^ r))

3. **`ostrowski_invariant_structured`**: Prove using:
   - For all r ∈ N_K \ {0,2,8}, displacement_condition r holds
   - This follows from the Ostrowski coefficient analysis (bₖ ≥ 1 at some k ≥ 5)

### Remaining challenges:
- Proving irrationality of log₃(2) (needed for infinite CF)
- Connecting Ostrowski coefficients to {r·α} bounds
- Characterizing φ⁻¹(C₃₀) in terms of fractional parts

## Testing Approach

### Verification layers:

| Layer | Method | What it verifies |
|-------|--------|------------------|
| Unit | `#eval` / `native_decide` | Individual lemmas (CF computation, digit extraction) |
| Integration | `lake build` | All components compile and type-check |
| Property | `decide` / `native_decide` | Displacement condition for specific r values |
| End-to-end | Existing proof chain | Bridge theorem, Erdős conjecture |

### Specific tests:

1. **CF computation test:**
   ```lean
   #eval (GenContFract.of (Real.logb 3 2)).convs 10
   -- Should converge to log₃(2) ≈ 0.6309
   ```

2. **Displacement condition test:**
   ```lean
   #eval displacement_condition 100
   -- Should be true (100 ∈ N_K for some K ≥ 12)
   ```

3. **Bridge theorem test:**
   ```lean
   #eval bridge_theorem 100
   -- Should be true (2^100 has digit 2 in ternary)
   ```

4. **Existing proof chain:**
   - `lake build` must succeed with zero sorry
   - All existing theorems must still hold
   - No new axioms introduced

### Regression testing:
- Run `lake build` after each component
- Verify `Mass1Dynamics.lean` still has zero sorry
- Verify `BridgeUniform.lean` still has zero sorry (except `ostrowski_invariant` axiom)

## Dependencies

- Component 1 depends on Mathlib continued fractions
- Component 2 depends on Component 1 + existing OstrowskiFormLemma
- Component 3 depends on existing Narkiewicz (memCantorNat)
- Component 4 depends on Components 2 + 3

## Timeline

- **Week 1:** Component 1 (ContinuedFraction/Log3.lean) - CF of α, irrationality
- **Week 2:** Component 2 (OstrowskiBridge.lean) - Bridge lemma
- **Week 3:** Component 3 (CantorAvoidance.lean) - Cantor characterization
- **Week 4:** Component 4 (DisplacementInterface.lean update) - Integration

## Success Criteria

1. `displacement_condition` defined with zero sorry
2. `displacement_implies_digit2` proved with zero sorry
3. `ostrowski_invariant_structured` proved (not axiom)
4. `lake build` succeeds with zero sorry
5. All existing theorems still hold
