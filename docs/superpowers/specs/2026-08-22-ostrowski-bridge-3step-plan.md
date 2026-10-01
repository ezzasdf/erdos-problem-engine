# Ostrowski Bridge Lemma: 3-Step Plan

**Date:** 2026-08-22
**Goal:** Eliminate `ostrowski_invariant` axiom from bridge proof with formal mathematical argument.

## Overview

Three-step plan to prove the bridge theorem for all K ≥ 12 without axioms:

1. **Ostrowski Pattern**: Prove the invariant holds for all N_K elements
2. **Separation Lemma**: Prove the invariant implies {r·α} avoids C_30
3. **Combine**: Chain 1 + 2 for the bridge theorem

---

## Step 1: Formalize Ostrowski Pattern

**Statement:** For all r ∈ N_K \ {0,2,8} with K ≥ 12, the Ostrowski expansion of r has at least one non-zero coefficient at position k ≥ 5.

**Approach:** Inductive proof via Saye recursion (NOT enumeration).

**Key insight:** N_{K+1} is derived from N_K by adding multiples of u_K = 2·3^{K-1}. If r ∈ N_K has b_k ≥ 1 at k ≥ 5, then at least one surviving extension r + i·u_K ∈ N_{K+1} also has b_k ≥ 1.

**Formalization plan:**

1. Define Ostrowski representation in Lean:
   ```lean
   def ostrowski_rep (n : Nat) : List Nat := ...
   ```

2. Define the invariant:
   ```lean
   def has_large_ostrowski (r : Nat) : Prop :=
     ∃ k ≥ 5, (ostrowski_rep r).getD k 0 ≥ 1
   ```

3. Prove base case K=12:
   - Use native_decide to verify all 2045 non-special residues
   - Or use the bridge_middle_K12 result directly

4. Prove inductive step K → K+1:
   - Show: if r ∈ N_K has the invariant, then at least one of
     {r, r+u_K, r+2u_K} ∈ N_{K+1} also has it
   - This uses Saye's recursion structure

**Challenges:**
- Computing Ostrowski representation in Lean is hard (greedy algorithm)
- Alternative: prove the property without computing the full representation
- Use the fact that q_k grows exponentially, so b_k ≥ 1 means r ≥ q_k

**Time estimate:** 1-2 days

---

## Step 2: Prove Separation Lemma

**Statement:** If r has a non-zero Ostrowski coefficient at position ≥ 5, then {r·α} avoids C_30.

**Mathematical argument:**

1. The continued fraction of α = log₃(2) has convergent denominators q_k
2. The fractional part satisfies: {q_k · α} ≈ (-1)^k / q_{k+1}
3. If b_k ≥ 1 at k ≥ 5, then r includes q_k in its representation
4. This shifts {r·α} by at least |{q_k · α}| ≈ 1/q_{k+1}
5. For k ≥ 5: q_6 = 19, so 1/q_6 ≈ 0.053
6. The Cantor set C_30 has gaps of size ~3^{-30} ≈ 10^{-14.3}
7. Since 0.053 ≫ 10^{-14.3}, {r·α} must be outside C_30

**Formalization plan:**

1. Define {r·α} in Lean:
   ```lean
   def frac_part (r : Nat) : Real :=
     (r : Real) * log 2 / log 3 - floor((r : Real) * log 2 / log 3)
   ```

2. Prove the Ostrowski expansion converges:
   ```lean
   theorem ostrowski_value_eq (n : Nat) :
     ostrowski_value log32_q (ostrowski_rep n) = n
   ```

3. Prove the fractional part bound:
   ```lean
   theorem frac_part_bound (r : Nat) (k : Nat) (hk : k ≥ 5)
       (hbk : (ostrowski_rep r).getD k 0 ≥ 1) :
     |frac_part r - nearest_c30_point| ≥ 1 / q_{k+1} - 3^{-30}
   ```

4. Connect to ternary digits:
   ```lean
   theorem frac_part_avoids_c30 (r : Nat) (h : has_large_ostrowski r) :
     ¬(memCantorNat (2 ^ r))
   ```

**Challenges:**
- Formalizing irrational arithmetic (α = log₃(2)) in Lean
- Bounding errors from higher-order Ostrowski terms
- Connecting {r·α} to ternary digits of 2^r

**Time estimate:** 3-5 days

---

## Step 3: Combine

**Statement:** For all K ≥ 12 and r ∈ N_K \ {0,2,8}, ¬(memCantorNat (2^r)).

**Proof:** Chain Step 1 + Step 2:
```lean
theorem bridge_ostrowski :
  ∀ K ≥ 12, ∀ r ∈ N_K \ {0,2,8}, ¬(memCantorNat (2 ^ r)) := by
  intro K hK r hr h0 h2 h8
  have h1 := ostrowski_pattern K hK r hr h0 h2 h8  -- Step 1
  exact separation_lemma r h1  -- Step 2
```

**Time estimate:** 1 hour

---

## Difficulty Ranking

| Step | Difficulty | Time | Bottleneck |
|------|-----------|------|------------|
| Step 1 (Pattern) | Hard | 1-2 days | Saye recursion ↔ Ostrowski connection |
| Step 2 (Separation) | Very Hard | 3-5 days | Irrational arithmetic in Lean |
| Step 3 (Combine) | Easy | 1 hour | Just chaining |

## Alternative Shortcut

If Step 2 proves too hard:
1. Prove Step 1 inductively (via Saye recursion)
2. Use native_decide for K=12 base case of Separation Lemma
3. This gives the bridge theorem without the full Separation Lemma

---

## Files to Modify

- `ErdosTernary/Ostrowski.lean`: Add Ostrowski representation definition
- New file `ErdosTernary/BridgeOstrowskiProof.lean`: Steps 1-3
- `ErdosTernary/BridgeUniform.lean`: Remove ostrowski_invariant axiom

## Success Criteria

- Bridge theorem proved for all K ≥ 5, r ∈ N_K \ {0,2,8}
- No axioms used in bridge proof (erdos_conjecture and ostrowski_invariant removed)
- Full project builds with zero sorry
