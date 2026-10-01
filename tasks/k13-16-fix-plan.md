# Plan: Fix K=13-16 Mass-1 Emptiness Proofs

## Problem

`mass1_in_NK_empty_K13` through `K16` are `sorry` because `native_decide` on `mass1_in_NK K = []` requires computing `computeNK K`, which iterates over u_K residues (u_13=1M, u_16=28M). Each requires `2^r % 3^K` — infeasible in the kernel.

## Solution: Direct Candidate Check

Instead of filtering all of N_K, enumerate the 304 mass-1 candidates and verify none lie in N_K.

**Key insight:** `mass1_in_NK K = []` iff for every candidate c = Q(j)+ℓ (j∈[5,20], ℓ∈[0,18]):
- either c ≥ u_K (not a valid residue), or
- `2^c % 3^K` has a digit 2 in its ternary expansion

This requires only 304 modular exponentiations instead of u_K.

## Implementation Steps

### Task 1: Add `powMod` to Mass1Dynamics.lean
Write a square-and-multiply modular exponentiation function:
```lean
def powMod (base exp modulus : Nat) : Nat
```
Tail-recursive, O(log exp) multiplications, each bounded by modulus².
For c≈135M and modulus=3^16≈43M, each multiplication fits in 64 bits.

### Task 2: Add `candidateMass1InNK` predicate
```lean
def candidateMass1InNK (K : Nat) (c : Nat) : Bool :=
  c < uK K && !hasTrailingDigit2 (powMod 2 c (3^K)) K
```
Checks if a single mass-1 candidate c lies in N_K.

### Task 3: Add `anyMass1InNK` boolean oracle
```lean
def anyMass1InNK (K : Nat) : Bool :=
  (List.range 16).any fun j =>
    (List.range 19).any fun l =>
      candidateMass1InNK K (Q Al32 (j + 5) + l)
```
Iterates over all 304 mass-1 candidates (j=5..20, ℓ=0..18).

### Task 4: Prove equivalence
```lean
theorem mass1_in_NK_eq_any (K : Nat) (hK : K ≤ 16) :
    mass1_in_NK K = [] ↔ anyMass1InNK K = false
```
Uses `isMassOneFormB'_iff'` (j≤20 bound for K≤16) and the definition of `computeNK`.

### Task 5: Replace sorry with native_decide
```lean
theorem mass1_in_NK_empty_K13 : mass1_in_NK 13 = [] := by
  rw [mass1_in_NK_eq_any (by omega)]
  native_decide
```
Same for K=14,15,16.

### Task 6: Build verification
Run `lake build` to confirm all 4 theorems pass.

## Complexity Analysis
- K=12: existing proof (u_12=354K residues in kernel) ✓
- K=13: 304 candidates × ~27 powMod iterations = ~8K ops (vs 1M in kernel)
- K=16: 304 candidates × ~25 powMod iterations = ~7.6K ops (vs 28M in kernel)

## Risk
- `powMod` with large exponents (c≈135M) in native_decide: should be fine since GMP handles this, but if not, we can bound exponents using `c % u_K` periodicity (2^c mod 3^K = 2^(c%u_K) mod 3^K).

## Files Modified
- `ErdosTernary/ErdosTernary/Mass1Dynamics.lean` (Tasks 1-5)
