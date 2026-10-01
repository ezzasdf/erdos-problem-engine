# Plan: Eliminate NK_15_eq, NK_16_eq, NK_17_eq Axioms

## Goal
Remove the 3 remaining NK axioms from BridgeK15/16/17.lean by proving `checkBridgeCantorPow2 K = true` directly via chunked range checks, then chaining with `checkBridgeCantorPow2_imp_not_cantor` from BridgeUniform.lean.

## Approach: Range-Chunked Bridge Verification

### Core Insight
Instead of proving `NK_K = computeNKFast K` (list equality over 16K+ elements), prove `checkBridgeCantorPow2 K = true` by splitting [0, uK K) into ranges of size chunk_size = 3^13 = 1,594,323. Each range is checked independently by native_decide. Coverage follows from arithmetic (ranges partition [0, uK K)).

### Key Numbers
| K | uK K = 2*3^(K-1) | chunk_size = 3^13 | num_chunks |
|---|---|---|---|
| 15 | 9,565,938 | 1,594,323 | 6 |
| 16 | 29,296,314 | 1,594,323 | 18 |
| 17 | 87,888,942 | 1,594,323 | 54 |

Total: 78 native_decide calls.

## Step 1: Create `BridgeCantorChunked.lean`

Location: `ErdosTernary/ErdosTernary/BridgeCantorChunked.lean`

```lean
import ErdosTernary.BridgeCompute

namespace ErdosTernary.BridgeCantorChunked
open ErdosTernary.BridgeCompute

/-- Range-parallel bridge check: for s in [0, hi-lo),
    if s+lo passes the trailing-2-free filter, check bridge property. -/
def rangeCheck (K lo hi : Nat) : Bool :=
  ((List.range (hi - lo)).filter (fun s =>
    !hasTrailingDigit2 (pow2Mod (s + lo) (3^K)) K
  )).all fun s =>
    (s + lo) == 0 || (s + lo) == 2 || (s + lo) == 8 ||
    hasDigit2UpTo (pow2Mod (s + lo) (3^50)) 50

/-- If rangeCheck is true, elements in [lo, hi) ∩ computeNKFast K
    satisfy the bridge property. -/
theorem rangeCheck_imp {K lo hi r : Nat}
    (hlo : lo ≤ r) (hhi : r < hi)
    (hr_nk : r ∈ computeNKFast K)
    (hcheck : rangeCheck K lo hi = true) :
    (r == 0 || r == 2 || r == 8 ||
     hasDigit2UpTo (pow2Mod r (3^50)) 50) = true := by
  unfold rangeCheck at hcheck
  have hall := List.all_eq_true.mp hcheck
  have hs : r - lo < hi - lo := by omega
  apply hall
  rw [List.mem_filter]
  refine ⟨List.mem_range.mpr hs, ?_⟩
  rw [show (r - lo) + lo = r by omega]
  unfold computeNKFast at hr_nk
  rw [List.mem_filter] at hr_nk
  exact hr_nk.2

/-- If all chunks covering [0, uK K) pass rangeCheck,
    then checkBridgeCantorPow2 K = true. -/
theorem checkBridgeCantorPow2_of_chunked (K chunk_size num_chunks : Nat)
    (hdiv : uK K = chunk_size * num_chunks)
    (hchunks : ∀ j, j < num_chunks →
      rangeCheck K (j * chunk_size) ((j + 1) * chunk_size) = true) :
    checkBridgeCantorPow2 K = true := by
  unfold checkBridgeCantorPow2
  rw [List.all_eq_true]
  intro r hr
  unfold computeNKFast at hr
  rw [List.mem_filter] at hr
  obtain ⟨r_lt, r_no2⟩ := hr
  rw [List.mem_range] at r_lt
  have hj : r / chunk_size < num_chunks := by omega
  have hcheck := hchunks (r / chunk_size) hj
  unfold rangeCheck at hcheck
  have hall := List.all_eq_true.mp hcheck
  apply hall
  rw [List.mem_filter]
  refine ⟨List.mem_range.mpr (by omega), ?_⟩
  rw [show (r - r / chunk_size * chunk_size) + r / chunk_size * chunk_size = r by omega]
  exact r_no2

end ErdosTernary.BridgeCantorChunked
```

## Step 2: Generate Per-Chunk Theorems (Python Script)

Create `gen_chunked_rangechecks.py` that outputs Lean code:

For each K in {15, 16, 17}:
```
set_option maxHeartbeats 20000000 in
private theorem rc_K{K}_chunk{i} :
    rangeCheck {K} {i * chunk_size} {(i+1) * chunk_size} = true := by
  native_decide
```

Then:
```
theorem checkBridgeCantorPow2_K{K} : checkBridgeCantorPow2 {K} = true :=
  checkBridgeCantorPow2_of_chunked {K} chunk_size num_chunks
    (by native_decide)  -- or omega
    (fun j hj => by
      interval_cases j <;> native_decide)
```

Wait, `interval_cases j` with 54 cases for K=17 is a lot. Better: generate explicit per-chunk theorems and chain them.

Actually, the cleanest approach: generate a single Python script that produces a Lean file with explicit per-chunk theorems AND a combined theorem.

For the combined theorem, instead of using `interval_cases`, generate:
```
theorem checkBridgeCantorPow2_K{K} : checkBridgeCantorPow2 {K} = true :=
  checkBridgeCantorPow2_of_chunked {K} chunk_size num_chunks
    (by native_decide)
    (fun j hj => by
      have := List.mem_range.mp (List.range(num_chunks) |>.mem_iff.mpr (by omega))
      -- Use a decision procedure or explicit lookup
      ...)
```

This is tricky. Alternative: define a lookup function:

```lean
private def chunk_proof (K j : Nat) (hj : j < num_chunks) :
    rangeCheck K (j * chunk_size) ((j+1) * chunk_size) = true := by
  ...
```

But this can't use native_decide because j is universally quantified.

**Best approach**: Use `native_decide` directly on the full `checkBridgeCantorPow2 K` but with `maxHeartbeats` set high. If native_decide on the full check (which internally computes `computeNKFast K`) is too slow/OOM, fall back to the chunked approach.

Actually, the whole point is that native_decide on `checkBridgeCantorPow2 K` FAILS because computing `computeNKFast K` requires iterating over uK K elements (up to 87M for K=17).

So we must use the chunked approach. The question is how to structure the proof that all chunks pass.

**Practical solution**: Generate explicit theorem per chunk, then in the combined theorem, convert j to a concrete value via omega and dispatch to the right theorem.

Actually, the simplest working approach:

```lean
theorem checkBridgeCantorPow2_K15 : checkBridgeCantorPow2 15 = true :=
  checkBridgeCantorPow2_of_chunked 15 chunk_size 6
    (by native_decide)
    (by intro j hj; interval_cases j <;> exact by assumption)
```

Where `by assumption` resolves to the appropriate per-chunk theorem. But `interval_cases j` for j < 6 gives 6 goals, each with a concrete j value, and `exact rc_K15_chunk0_hyp` etc. resolves them.

For K=17 with 54 chunks, `interval_cases j` gives 54 goals. Each is dispatched by `exact rc_K17_chunk{i}_hyp`. This should work!

The Python script generates:
1. Per-chunk theorems (78 total)
2. A combined theorem using `interval_cases`

## Step 3: Modify BridgeK15/16/17.lean

For each K, replace the axiom-based proof:

```lean
-- OLD (axiom):
axiom NK_15_eq : NK_15 = computeNKFast 15
theorem bridge_K15_not_cantor (r : Nat)
    (hr : r ∈ computeNKFast 15) (hSpecial : ...) :
    ¬(memCantorNat (2 ^ r)) := by
  have hr15 : r ∈ NK_15 := by rwa [NK_15_eq]
  ...

-- NEW (axiom-free):
theorem bridge_K15_not_cantor (r : Nat)
    (hr : r ∈ computeNKFast 15) (hSpecial : ...) :
    ¬(memCantorNat (2 ^ r)) :=
  checkBridgeCantorPow2_imp_not_cantor 15
    checkBridgeCantorPow2_K15 r hr hSpecial
```

This eliminates `NK_15_eq`, `NK_16_eq`, `NK_17_eq` axioms entirely!

## Step 4: Verify on Cloud

Push to cloud-clean branch and run full build:
```bash
~/bin/gh codespace ssh -c erdos-build-rxxgg9j65973pv6j -- \
  'bash -l -c "cd /workspaces/erdos-problem-engine/ErdosTernary && lake build ErdosTernary.BridgeCantorChunked && lake build ErdosTernary.BridgeUniform"'
```

## Expected Outcome
- 3 axioms eliminated (NK_15_eq, NK_16_eq, NK_17_eq)
- 1 axiom remains (ostrowski_invariant)
- Total axiom count: 4 → 1
- 78 native_decide calls for the range checks

## Risk: native_decide on chunk_size=3^13
If native_decide fails on chunks of 1.5M elements, reduce to chunk_size=3^12=531,441 (18+54+162=234 chunks) or 3^11=177,147 (54+162+486=702 chunks).

## Files to Create/Modify
1. **CREATE**: `ErdosTernary/ErdosTernary/BridgeCantorChunked.lean` - infrastructure + chunk proofs
2. **CREATE**: `ErdosTernary/gen_chunked_rangechecks.py` - Python generator for per-chunk theorems
3. **MODIFY**: `ErdosTernary/ErdosTernary/BridgeK15.lean` - remove NK_15_eq axiom, rewrite bridge_K15_not_cantor
4. **MODIFY**: `ErdosTernary/ErdosTernary/BridgeK16.lean` - remove NK_16_eq axiom, rewrite bridge_K16_not_cantor
5. **MODIFY**: `ErdosTernary/ErdosTernary/BridgeK17.lean` - remove NK_17_eq axiom, rewrite bridge_K17_not_cantor
6. **MODIFY**: `ErdosTernary/ErdosTernary/BridgeUniform.lean` - add import for BridgeCantorChunked
