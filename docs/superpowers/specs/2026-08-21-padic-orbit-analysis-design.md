# Design Spec: p-Adic Orbit-Cantor Intersection Analysis

Date: 2026-08-21. Goal: understand why the ×2 orbit in ℤ₃ intersects the Cantor set Σ_{3,2} in exactly {0, 2, 8}.

## Background

The Erdős Ternary Conjecture (1978): the only n with 2^n having no digit 2 in base 3 are n ∈ {0, 2, 8}.

Computational verification: K=40 (n ≤ 8.1×10^18), same 3 survivors at every K tested (10 through 40).

Saye's branching lemma (formalized in Lean) says at most 2 of 3 branches survive at each level k → k+1. But it doesn't explain why the tree collapses to exactly 3 survivors.

## Goal

Compute the intersection of the ×2 orbit with the Cantor set at each p-adic level k, track how the survival set shrinks, and formulate an algebraic conjecture explaining the 3-survivor phenomenon.

## Approach

### Step 1: Orbit-Cantor Intersection Computation

For each k from 1 to 20:

1. **Cantor residues C_k**: the set of residues r ∈ {0, ..., 3^k - 1} whose base-3 expansion uses only digits 0 and 1. |C_k| = 2^k.

2. **Cantor units**: C_k ∩ (ℤ/3^kℤ)^× (excluding multiples of 3). Since all Cantor residues with digit_0 ∈ {0, 1} and at least one non-zero digit are units, |C_k ∩ (ℤ/3^kℤ)^×| = 2^k - 1 (excluding r=0).

3. **Orbit**: {2^n mod 3^k : n = 0, 1, ..., u_k - 1} where u_k = 2·3^{k-1}. Since 2 is a primitive root mod 3^k, this is all of (ℤ/3^kℤ)^×.

4. **Intersection**: N_k = {n mod u_k : 2^n mod 3^k ∈ C_k ∩ (ℤ/3^kℤ)^×}. This is the set of n (mod u_k) for which 2^n is Cantor in the last k ternary digits.

5. **Refined intersection**: S_k = {n : 2^n mod 3^j ∈ C_j for all j ≤ k}. This is the "survival set" — n survives if and only if 2^n is Cantor at every level up to k.

### Step 2: Pattern Analysis

Track:
- |N_k| (how many residues mod u_k are Cantor at level k)
- |S_k| (how many n mod lcm(u_1, ..., u_k) survive all levels up to k)
- The ratio |N_k| / u_k (should approach (2/3)^{k-1} by the density law)
- The rate at which |S_k| decreases
- Whether S_k always contains {0, 2, 8} (mod u_k)
- Whether S_k ever contains anything else for k ≥ some threshold

### Step 3: Algebraic Characterization

Look for:
- A multiplicative characterization of C_k ∩ (ℤ/3^kℤ)^× (not just digit-based)
- The relationship between C_k and the kernel of ×2 mod 3^k
- A "collapsing invariant" — a property of the orbit that forces narrowing
- Whether the 3 survivors {0, 2, 8} correspond to a specific algebraic structure (e.g., a subgroup)

### Step 4: Conjecture Formulation

Based on the data, formulate:
- A precise algebraic statement about why only {0, 2, 8} survive
- A potential proof strategy (even if incomplete)
- What would need to be formalized in Lean

## Implementation

**Language**: Python 3 (no external dependencies beyond stdlib)

**Output**: 
- `verify_middle/padic_orbit_analysis.py` — the analysis script
- `verify_middle/PADIC_ORBIT_FINDINGS.md` — findings document

**Computational limits**:
- k ≤ 20 (3^20 ≈ 3.5×10^9, feasible)
- u_k = 2·3^{k-1}, max u_20 = 2·3^19 ≈ 2.3×10^9
- S_k computation requires checking all j ≤ k, so cumulative but bounded

## Success Criteria

1. A table of |N_k|, |S_k|, and ratios for k = 1..20
2. A clear pattern in how S_k shrinks
3. An algebraic characterization (even partial) of the Cantor units
4. A conjecture statement
5. A findings document suitable for future Lean formalization
