# Plan: Option 2 — Ostrowski Coefficient Analysis for K=5..15

## Context

The bridge theorem needs: for r ∈ N_K \ {0,2,8}, {r·α} ∉ φ^{-1}(C_30).

**Key insight:** For every r ∈ N_K (K=5..15), compute its Ostrowski coefficients and determine the first coefficient at which the resulting interval for {r·α} becomes disjoint from C_30.

This is the "key to solve all" — if we find a structural pattern in the Ostrowski coefficients of N_K elements, we can replace the `erdos_conjecture` axiom with a proof.

## Task 1: Deep Ostrowski Analysis Script

**File:** `verify_middle/ostrowski_bridge_deep.py`

### Algorithm

For each K = 5, 6, ..., 15:
1. Compute N_K (trailing 2-free residues, |N_K| = 2^{K-1})
2. For each r ∈ N_K \ {0, 2, 8}:
   a. Compute Ostrowski representation: r = Σ b_k * q_k
   b. Compute {r·α} with 200-digit precision
   c. For L = 1 to 30:
      - Compute the set S(r, L) = {{r·α} : r has this Ostrowski prefix of length L}
      - Check if S(r, L) ∩ φ^{-1}(C_L) = ∅
      - Record first L where disjointness occurs
   d. Record: (K, r, first_disjoint_L, Ostrowski_prefix, {r·α})

### Output

Table format:
```
K | r | |N_K| | Ostrowski prefix | {r·α} | first_disjoint_L | notes
5 | 9  | 16  | [0,0,1,0,...]   | 0.123 | 12              | ...
```

Also output:
- Minimum disjoint L across all (K, r)
- Most common Ostrowski prefixes that cause disjointness
- Pattern analysis: do certain coefficient values always cause disjointness?

## Task 2: Pattern Analysis

**File:** `verify_middle/ostrowski_pattern_analysis.py`

Analyze the output from Task 1:

1. **Minimum L**: What is the smallest L such that for ALL r ∈ N_K \ {0,2,8} (K=5..15), {r·α} ∉ φ^{-1}(C_L)?
   - If L ≤ 30, this proves the bridge theorem for K=5..15

2. **Coefficient patterns**: Which Ostrowski coefficients b_k are non-zero for N_K elements?
   - Do certain positions always have b_k = 0?
   - Do certain values of b_k always cause disjointness?

3. **Interval width**: How does the interval I(r, L) shrink as L increases?
   - I(r, L) is determined by the first L Ostrowski coefficients
   - Width ≈ 1/q_{L+1} (from continued fraction theory)

4. **Disjointness criterion**: What is the mathematical condition for I(r, L) ∩ φ^{-1}(C_L) = ∅?
   - Relates to the ternary expansion of 3^{{r·α}}
   - First L digits must contain a 2

## Task 3: Lean Formalization

**File:** `ErdosTernary/ErdosTernary/BridgeOstrowski.lean`

### Approach A: Interval Arithmetic (if clean pattern found)

```lean
-- Define Ostrowski representation
def ostrowskiRep (n : Nat) (q : List Nat) : List Nat := ...

-- Prove bound on {n·α} using Ostrowski coefficients
theorem frac_part_bound (n : Nat) (b : List Nat) (q : List Nat) :
    {n * α} ∈ interval_from_ostrowski b q

-- Prove interval excludes φ^{-1}(C_30)
theorem interval_excludes_cantor (K : Nat) (r : Nat) (hr : r ∈ N_K) (hrne : r ∉ {0,2,8}) :
    interval_from_ostrowski (ostrowskiRep r q) q ∩ φ_inv_C30 = ∅
```

### Approach B: Finite Case Analysis (if no clean pattern)

For K=5..15: verify by native_decide (already done for K=5..9).
For K≥16: use the Python analysis as computational evidence, state as axiom.

### Approach C: Hybrid (most likely)

1. Formalize the Ostrowski representation in Lean
2. Formalize the interval bound theorem
3. For K=5..15: verify by native_decide or by the interval bound
4. For K≥16: state the pattern as an axiom, with computational evidence

## Task 4: Replace erdos_conjecture Axiom

If the Ostrowski analysis reveals a provable pattern:

1. Prove `ostrowski_bridge_lemma`: for all K ≥ 5 and r ∈ N_K \ {0,2,8}, {r·α} ∉ φ^{-1}(C_30)
2. From this, derive `¬(memCantorNat (2^r))` without erdos_conjecture
3. Update `BridgeUniform.lean` to use the new lemma instead of erdos_conjecture
4. Remove the axiom (or weaken it significantly)

## Key Mathematical Details

### Continued Fraction of α = log_3(2)

From `p_cf_log32.py`:
```
α = [0; 1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, ...]
```

Convergent denominators: q = [1, 1, 2, 3, 8, 24, 32, 184, 400, 9384, ...]

### Ostrowski Representation

For n = Σ b_k * q_k:
- 0 ≤ b_k ≤ a_{k+1} (partial quotient)
- No two consecutive b_k are both equal to a_{k+1}

### Fractional Part Formula

{n·α} = Σ b_k * {q_k·α} (mod 1)

Since {q_k·α} ≈ (-1)^k / q_{k+1}, the sum is an alternating series.

### Cantor Set C_L

C_L = {x ∈ [0,1) : first L ternary digits of 3^x contain no 2}

This is a union of 2^L intervals, each of width ≈ 3^{-L}.

## Constraints

- **K ≤ 15**: u_15 ≈ 2.4×10^7, |N_15| = 16384. Feasible for computation.
- **Precision**: Need 200+ digits for {r·α} computation
- **Time**: Python analysis ~1 hour, Lean formalization ~1-2 weeks

## Success Criteria

1. Python script produces complete table for K=5..15
2. Pattern analysis reveals structural reason for bridge theorem
3. Lean formalization replaces erdos_conjecture axiom (or weakens it significantly)
4. Full project builds with zero sorry and reduced axioms

## Risk Assessment

- **High reward**: If this works, it's a breakthrough in the Erdős conjecture
- **High risk**: The Ostrowski structure may not reveal a clean pattern
- **Fallback**: Use Python analysis as computational evidence, keep axiom for K≥16
- **Time estimate**: 1-2 days for analysis, 1-2 weeks for formalization

## Dependencies

- Existing `ostrowski_analysis.py` and `ostrowski_bridge.py`
- `p_cf_log32.py` for continued fraction data
- `bridge_induction_check.py` for N_K computation
- Mathlib4 v4.12.0 for Lean formalization
