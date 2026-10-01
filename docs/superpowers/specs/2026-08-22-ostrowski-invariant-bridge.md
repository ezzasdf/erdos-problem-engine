# Ostrowski Invariant Bridge Lemma — Design Spec

**Date:** 2026-08-22
**Goal:** Eliminate `erdos_conjecture` axiom from bridge proof, replacing it with structural Ostrowski argument.

## The Problem

The bridge theorem (`bridge_first_period_all` in BridgeUniform.lean) currently uses `erdos_conjecture` axiom for r ≥ 1001. This makes the proof circular — it assumes what it aims to prove.

## Key Discovery

**Invariant:** For all r ∈ N_K \ {0,2,8} with K ≥ 12, there exists k ≥ 5 such that the Ostrowski coefficient b_k(r) ≥ 1.

**Computational verification:**
- K=12: 2045 non-special residues, 0 violations
- K=13: 4093 non-special residues, 0 violations
- K=14: 8189 non-special residues, 0 violations
- K=15: 16381 non-special residues, 0 violations

**Why it works:**
- Convergent denominators q_k grow exponentially: q_5=8, q_6=19, q_7=65, q_8=84, q_9=485, q_10=1054
- If b_k ≥ 1 for some k ≥ 5, then r includes q_k in its Ostrowski representation
- The fractional part {q_k · α} ≈ (-1)^k / q_{k+1} is a "large" shift (~0.125 for k=5)
- This shift forces {r · α} away from the thin Cantor set C_30 (measure (2/3)^30 ≈ 4.7×10^{-6})
- Special values 0, 2, 8 have b_k = 0 for all k ≥ 5 (their representations use only q_0..q_4)

## Proof Structure

### Phase A: Formalize Ostrowski Invariant (Ostrowski.lean)

1. Define `hasLargeOstrowskiCoeff (r : Nat) : Prop := ∃ k ≥ 5, b_k(r) ≥ 1`
2. Prove base case K=12 by enumerating NK_12's coefficients (2045 elements)
3. Prove: `special_values (0,2,8) do NOT have large coefficients`

### Phase B: Bridge Consequence

Prove: `hasLargeOstrowskiCoeff r → ¬(memCantorNat (2^r))`

This requires:
1. Formalizing the connection between Ostrowski coefficients and {r · α}
2. Showing that b_k ≥ 1 at k ≥ 5 forces {r · α} outside φ^{-1}(C_30)
3. Using the identity: leading L ternary digits of 2^n = leading L ternary digits of 3^{{n · α}}

### Phase C: Inductive Step (K → K+1)

Show: if r ∈ N_K has the invariant, then at least one of {r, r+u_K, r+2u_K} ∈ N_{K+1} also has it.

This uses Saye's recursion to relate N_{K+1} to N_K.

### Phase D: Wire into BridgeUniform.lean

1. Replace `pow2_not_cantor_for_large` with the Ostrowski-based proof
2. Remove `erdos_conjecture` axiom usage for r ≥ 1001
3. Keep `erdos_conjecture` as isolated placeholder only

## Lean Files to Modify

- `ErdosTernary/Ostrowski.lean`: Add invariant definition and base case proof
- New file `ErdosTernary/BridgeOstrowskiInvariant.lean`: Bridge consequence and inductive step
- `ErdosTernary/BridgeUniform.lean`: Wire in new proof, remove axiom usage

## Risks and Mitigations

1. **Risk:** Formalizing {r · α} in Lean requires irrational arithmetic
   **Mitigation:** Use high-precision rational approximations of α = log₃(2)

2. **Risk:** Inductive step may be complex
   **Mitigation:** Start with K=12 base case, defer induction if needed

3. **Risk:** Bridge consequence proof may need heavy real analysis
   **Mitigation:** Focus on the computational certificate approach (verify for K=12, use induction for K≥13)

## Success Criteria

- Bridge theorem proved for all K ≥ 5, r ∈ N_K \ {0,2,8}, with zero sorry
- `erdos_conjecture` axiom isolated as placeholder only (not used in bridge proof)
- No enumeration of K ≥ 13 lists
- K=12 as formal base case
