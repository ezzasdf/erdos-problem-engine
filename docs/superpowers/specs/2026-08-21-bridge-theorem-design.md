# Design Spec: Phase 12 — Leading/Trailing Orbit Intersection (Bridge Theorem)

Date: 2026-08-21. Goal: find arithmetic correlations between leading and trailing ternary digits of 2^n that could become a bridge theorem.

## Background

Phase 11 showed that trailing-depth nesting is tautological (S_k = N_k). The missing information must come from the **interaction** between leading and trailing digits. Both sides are implemented in the Rust two-sided engine (Phase 9/10), but the engine only reports aggregate counts — not per-candidate signatures.

## Definitions

For a candidate n:
- **B_K(n)** = {last K ternary digits of 2^n avoid 2} (trailing, 3-adic side)
- **A_L(n)** = {first L ternary digits of 2^n avoid 2} (leading, real side)
- **A_L ∩ B_K** = candidates surviving both checks

For each n in A_L ∩ B_K, record the signature:
- n (the candidate itself)
- n mod u_K (trailing residue class, u_K = 2·3^{K-1})
- {n·α} (fractional part of n·log₃2, where α = log₃2)
- leading_prefix: first L ternary digits of 2^n (string of 0s and 1s)
- trailing_suffix: last K ternary digits of 2^n (string of 0s and 1s)

## Goal

Find a bridge theorem of one of two forms:

1. **Trailing → Leading:** B_K(n) ⟹ {n·α} ∈ I_K for some explicitly shrinking set I_K
2. **Leading → Trailing:** A_L(n) ⟹ n mod u_K ∈ R_{L,K} for some residue set R_{L,K}

Either direction connects the real and 3-adic sides and could become an infinite proof.

## Approach

### Step 1: Python Data Collection (K ≤ 15)

Script: `verify_middle/bridge_analysis.py`

For each K from 5 to 15:
1. Compute all n in [0, u_K) where B_K(n) holds (trailing 2-free in last K digits)
2. For each such n, check A_L(n) for L = 10, 20, 30, 40, 50, 60, 70
3. Record the signature: (n, n mod u_K, {n·α}, leading_prefix, trailing_suffix)
4. Export to CSV: `verify_middle/bridge_data_K{K}.csv`

The leading check uses the same interval-arithmetic approach as the Rust engine:
- Compute frac = {n·α} as a rational interval [flo/S, fhi/S] at scale S = 3^P
- Compute 3^frac via Taylor expansion (certified bounds)
- Extract the first L ternary digits
- Check for digit 2

### Step 2: Python Correlation Analysis

For each (L, K) pair in the collected data:

1. **Joint distribution:** plot (n mod u_K) vs {n·α} for all survivors
2. **Conditional distributions:**
   - Given B_K(n): what is the distribution of {n·α}?
   - Given A_L(n): what is the distribution of n mod u_K?
3. **Independence test:** are leading and trailing sides independent?
   - If independent: the bridge theorem doesn't exist (or is trivial)
   - If dependent: there's a correlation to exploit
4. **Shrinking set detection:** does the set of {n·α} values for B_K-survivors shrink as K increases?
5. **Residue class detection:** does the set of n mod u_K values for A_L-survivors shrink as L increases?

### Step 3: Bridge Conjecture Formulation

Based on the correlation data:
- Formulate a precise statement about the leading/trailing interaction
- State it as a theorem candidate
- Assess provability (can it be proved from existing tools, or does it require new methods?)

### Step 4: Rust Data Collection (K ≥ 20, if patterns found)

Add a `--signatures` flag to the two-sided engine:
- For each candidate n, write a CSV row: n, n_mod_uk, frac_lo, frac_hi, leading_prefix, trailing_suffix
- Run at K=20, K=25, K=30 to validate patterns at scale

## Implementation

**Language:** Python 3 (Steps 1-3), Rust (Step 4)
**Dependencies:** Python stdlib only for Steps 1-3
**Output:** CSV files + findings markdown

## Success Criteria

1. A dataset of signatures for all survivors at K ≤ 15 and multiple L values
2. A clear statement about independence or dependence of leading/trailing sides
3. A bridge conjecture (even if unproved)
4. If patterns found: Rust implementation for validation at larger K

## Key Functions (reuse from existing code)

- `padic_orbit_analysis.py::orbit_cantor_intersection(K)` — B_K survivors
- `leading.rs::leading_digits_have_two(n, k_prime)` — A_L check (Rust)
- `leading.rs::certified_alpha(p)` — α as certified interval
- `leading.rs::digits_of(v, p)` — extract base-3 digits from BigInt
- Python equivalent of leading check: compute {n·α} and 3^{frac} via interval arithmetic
