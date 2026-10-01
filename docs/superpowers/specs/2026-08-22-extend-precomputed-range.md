# Option 1: Extend Precomputed Range to N=1000

## Problem Statement

The bridge theorem proof in `BridgeUniform.lean` splits at r=48:
- r < 48: proved by `native_decide` (via `check_nine_to_47`)
- r ≥ 48: uses `erdos_conjecture` axiom (circular)

We need to extend the precomputed range from N=47 to N=1000, pushing the axiom split from r=48 to r=1001.

## Mathematical Foundation

For each n ∈ [9, 1000], we need to prove:
```
hasLeadingDigit2 (2^n) 30 = true
```

This means: the first 30 ternary digits of 2^n contain a digit 2.

The proof strategy:
1. Compute 2^n as a big integer (Python can handle this for n ≤ 1000)
2. Convert 2^n to ternary
3. Find the first position i where digit = 2
4. Generate Lean proof term: `⟨i, by omega, by native_decide⟩`

## Implementation Plan

### Step 1: Python Proof Generator

Create `verify_middle/generate_bridge_proofs.py`:
- For n in range(48, 1001):
  - Compute 2^n using Python big integers
  - Convert to ternary representation
  - Find first position i where digit = 2
  - Generate Lean proof term for `hasLeadingDigit2 (2^n) 30 = true`
- Output: Lean source file with all proof terms

### Step 2: Lean File Generation

Create `ErdosTernary/ErdosTernary/BridgeComputeExtended.lean`:
- Import Mathlib and existing modules
- Define `check_leading_48_to_1000`: `List.all` over n=48..1000
- Prove by `native_decide` (if feasible) or by concatenating individual proofs
- Prove `all_48_to_1000_has_digit2`: ∀ n ∈ [48, 1000], hasLeadingDigit2 (2^n) 30 = true

### Step 3: Update BridgeUniform.lean

Modify `bridge_small_n` and `bridge_all_K_digit2`:
- Change split point from 48 to 1001
- Use `all_48_to_1000_has_digit2` for r < 1001
- Keep `pow2_not_cantor_for_large` for r ≥ 1001 (still uses axiom)

## Constraints

- **n ≤ 1000**: 2^1000 ≈ 10^301, ~1000 ternary digits. Feasible for Python big integers.
- **native_decide feasibility**: The `List.all` over 953 elements (n=48..1000) may be too large for `native_decide`. Fallback: concatenate individual proof terms.
- **Proof term size**: Each n needs ~5 lines of Lean. Total ~5000 lines. Manageable.

## Success Criteria

1. `BridgeComputeExtended.lean` builds with zero sorry
2. `all_48_to_1000_has_digit2` is proved
3. `BridgeUniform.lean` builds with zero sorry (axiom still used for r ≥ 1001)
4. Full project builds: `lake build` succeeds

## Risk Assessment

- **Low risk**: This is a straightforward extension of existing infrastructure
- **Main risk**: `native_decide` may not handle 953 elements. Mitigation: use individual proof terms.
- **Time estimate**: 1-2 hours for implementation, 30 min for verification
