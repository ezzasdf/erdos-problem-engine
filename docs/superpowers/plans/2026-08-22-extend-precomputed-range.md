# Plan: Option 1 — Extend Precomputed Range to N=1000

## Context

The bridge theorem proof in `BridgeUniform.lean` has a circular dependency: it uses `erdos_conjecture` axiom for r ≥ 48 to prove itself. Extending the precomputed range pushes the axiom split point, buying time for Option 2 (the structural proof).

**Current state:**
- `check_nine_to_47`: native_decide for n ∈ [9, 47] — proves `hasLeadingDigit2 (2^n) 30 = true`
- `bridge_small_n`: uses the above for r < 48
- `pow2_not_cantor_for_large`: uses `erdos_conjecture` for r ≥ 48

**Goal:** Extend to n ∈ [9, 1000], changing the split from r=48 to r=1001.

## Task 1: Create Python Proof Generator

**File:** `verify_middle/generate_bridge_proofs.py`

For each n ∈ [48, 1000]:
1. Compute 2^n (Python big integer)
2. Convert to ternary: repeatedly divide by 3
3. Find first position i where digit = 2 (scanning from most significant)
4. Output Lean proof term

**Output format:**
```lean
theorem check_leading_48 : hasLeadingDigit2 (2 ^ 48) 30 = true := by
  -- 2^48 in ternary has digit 2 at position X
  native_decide

theorem check_leading_49 : hasLeadingDigit2 (2 ^ 49) 30 = true := by
  native_decide
-- ... for each n up to 1000
```

**Alternative approach (if native_decide too slow for individual proofs):**
Generate explicit witness:
```lean
theorem check_leading_48 : hasLeadingDigit2 (2 ^ 48) 30 = true := by
  unfold hasLeadingDigit2 toTernaryDigits
  simp
  exact ⟨i, by omega, by native_decide⟩
```

## Task 2: Create BridgeComputeExtended.lean

**File:** `ErdosTernary/ErdosTernary/BridgeComputeExtended.lean`

```lean
import Mathlib.Tactic
import ErdosTernary.BridgeCompute

-- Option A: Single native_decide (may work for 953 elements)
theorem check_leading_48_to_1000 :
    List.all ((List.range 1001).filter (· ≥ 48))
      (fun n => hasLeadingDigit2 (2 ^ n) 30) = true := by
  native_decide

-- Option B: Individual proofs concatenated
-- (if Option A fails)
```

## Task 3: Update BridgeUniform.lean

**Changes:**
1. Import `BridgeComputeExtended`
2. Add `all_48_to_1000_has_digit2`: ∀ n ∈ [48, 1000], ¬(memCantorNat (2^n))
3. Change `bridge_small_n` split from 48 to 1001
4. Change `bridge_all_K_digit2` split from 48 to 1001

**Before:**
```lean
theorem bridge_all_K_digit2 ... := by
  by_cases hr48 : r < 48
  · exact bridge_small_n K hK r hr hSpecial hr48
  · exact pow2_not_cantor_for_large r (by omega)
```

**After:**
```lean
theorem bridge_all_K_digit2 ... := by
  by_cases hr1001 : r < 1001
  · exact bridge_small_n K hK r hr hSpecial hr1001
  · exact pow2_not_cantor_for_large r (by omega)
```

## Task 4: Verify Build

Run:
```bash
cd ErdosTernary && lake build
```

Expected: Build succeeds with zero sorry.

## Execution Order

1. Create `generate_bridge_proofs.py` and run it
2. Create `BridgeComputeExtended.lean` with the generated proofs
3. Test `native_decide` feasibility for the combined theorem
4. Update `BridgeUniform.lean` with new split point
5. Run `lake build` to verify

## Dependencies

- Python 3 with standard library (no external deps)
- Lean 4 with mathlib4 v4.12.0
- Existing `BridgeCompute.lean` and `BridgeUniform.lean`

## Verification

- `lake build` succeeds
- `grep -r "sorry" ErdosTernary/` returns only the known axioms (not new ones)
- The axiom split point is now r=1001 instead of r=48
