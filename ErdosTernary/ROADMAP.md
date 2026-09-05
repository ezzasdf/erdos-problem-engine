# Erdos Ternary Conjecture — Formalization Roadmap

**Last updated:** 2026-09-05
**Lean version:** 4.x / Mathlib 4.x
**Build command:** `lake build`

---

## Current Status

| Module | Status | Sorries | Axioms |
|--------|--------|---------|--------|
| `Narkiewicz.lean` | Complete | 0 | 0 |
| `SayeLemma.lean` | Complete | 0 | 0 |
| `Ostrowski.lean` | Complete | 0 | 0 |
| `OstrowskiFormLemma.lean` | Complete | 0 | 0 |
| `ContinuedFraction/Log3.lean` | Complete | 0 | 0 |
| `RotationDecomp.lean` | Complete (committed `b8ade44`) | 0 | 0 |
| `BridgeCompute.lean` | Complete (K=5..9 native_decide) | 0 | 0 |
| `BridgeComputeExtended.lean` | Complete (r=48..1000 native_decide) | 0 | 0 |
| `Bridge.lean` | Complete (4 dead axioms removed) | 0 | 0 |
| `BridgeMiddle.lean` | Complete (K=10..12 native_decide) | 0 | 0 |
| `BridgeK13.lean` | Complete (K=13 List Nat candidates + native_decide) | 0 | 0 |
| `BridgeK14.lean` | Complete (K=14 Array Nat candidates + native_decide) | 0 | 0 |
| `BridgeK15.lean` | Complete (K=15 Array Nat candidates + native_decide) | 0 | 0 |
| `BridgeMiddle16.lean` | Complete (K=16 NK_16 List + native_decide) | 0 | 0 |
| `BridgeCandidates.lean` | Complete (K=13-16 Array Nat candidates + native_decide) | 0 | 0 |
| `BridgeUniform.lean` | **1 axiom** (`ostrowski_invariant`) | 0 | 1 |
| `MiddleDigits.lean` | Complete | 0 | 0 |
| `LeadingDigits.lean` | Complete | 0 | 0 |
| `OstrowskiAvoid.lean` | Complete | 0 | 0 |
| `Mass1Dynamics.lean` | Complete | 0 | 0 |
| `BridgeOstrowski.lean` | Complete | 0 | 0 |
| `BridgeOstrowskiInvariant.lean` | Complete | 0 | 0 |
| `DisplacementInterface.lean` | Complete (0 axioms — `ostrowski_invariant_structured` eliminated) | 0 | 0 |
| `TestDigit.lean` | Standalone test (unused) | 1 | 0 |

**Total real sorrys in main proof chain: 0**
**Total axioms in proof chain: 1** (`ostrowski_invariant` in BridgeUniform.lean)

---

## Architecture (Dependency Chain)

```
Narkiewicz, SayeLemma          ← Pure combinatorics (complete)
        ↓
Ostrowski                      ← Ostrowski representation theorem (complete)
        ↓
OstrowskiFormLemma             ← Q recurrence, gd, topIdx, Al32 (complete)
        ↓
ContinuedFraction/Log3         ← log₃(2) CF bounds, irrationality (complete)
        ↓
RotationDecomp.lean            ← CF↔Al32 bridge (sorry-free, committed b8ade44)
        ↓
LeadingDigits                  ← Digit correspondence
        ↓
BridgeCompute → BridgeMiddle → BridgeUniform → BridgeOstrowski
   (K=5..9)    (K=10..12)     (K≥13 axiom)     (re-export)
        ↓                        ↓
BridgeK13/K14/K15            NK_mono (proven)
BridgeMiddle16
BridgeCandidates
        ↓
Mass1Dynamics → BridgeOstrowskiInvariant
        ↓
OstrowskiAvoid                 ← Final Erdős corollary (sorry-free)
```

---

## Axiom Elimination Progress

### Eliminated

| Axiom | File | Method |
|-------|------|--------|
| `ostrowski_invariant_structured` | DisplacementInterface.lean:87 | Trivially identical to `displacement_implies_digit2` |
| `bridge_theorem` | Bridge.lean:136 | Dead code — never imported or used |
| `bridge_theorem_first_period` | Bridge.lean:150 | Dead code — never imported or used |
| `saye_intersection` | Bridge.lean:164 | Dead code — never imported or used |
| `erdos_conjecture` | Bridge.lean:177 | Dead code — never imported or used |

### Remaining

| Axiom | File | Used for | Current coverage |
|-------|------|----------|-----------------|
| `ostrowski_invariant` | BridgeUniform.lean:79 | K ≥ 13 in `bridge_all_K_digit2` | K=13,14,15,16 computationally verified; K≥17 needs new argument |

---

## The Single Axiom: `ostrowski_invariant`

```lean
axiom ostrowski_invariant :
  ∀ K, K ≥ 12 →
  ∀ r, r ∈ computeNK K → r ≠ 0 → r ≠ 2 → r ≠ 8 →
  ¬(memCantorNat (2 ^ r))
```

### Current coverage in `bridge_all_K_digit2`

| K range | Method | Status |
|---------|--------|--------|
| 5–9 | `checkBridgeCantor` via `native_decide` | ✅ Proven |
| 10–12 | `bridge_middle_not_cantor` via `checkMiddleBridgeList` native_decide | ✅ Proven |
| 13 | `bridge_K13_pow2mod` (BridgeK13.lean) + `NK_mono` | ✅ Proven |
| 14 | `bridge_K14_candidates` (BridgeK14.lean) | ✅ Proven |
| 15 | `bridge_K15_candidates` (BridgeK15.lean) | ✅ Proven |
| 16 | `bridge_middle_K16` (BridgeMiddle16.lean) | ✅ Proven |
| **≥17** | **`pow2_not_cantor_for_large_K`** → `ostrowski_invariant` | **AXIOM** |

### Key proven lemma: NK_mono

```lean
theorem NK_mono {K₁ K₂ r : Nat} (hK : K₁ ≤ K₂) (hbound : r < uK K₁) :
    r ∈ computeNK K₂ → r ∈ computeNK K₁
```

If r survives the trailing-2-free filter at level K₂, it also survives at any lower level K₁ ≤ K₂ (assuming r < uK K₁). This allows reducing K≥17 to K=13 for r < uK 13 ≈ 1,062,882.

### Remaining gap: K ≥ 17, r ≥ uK 13

For K ≥ 17 and r ∈ computeNK K with r ≥ uK 13:
- NK_mono cannot reduce to K=13 (bound r < uK 13 not satisfied)
- Need either computational verification for K=17+ or number-theoretic argument

---

## Next Step: Number-Theoretic Approach

### Core idea

For r ∈ computeNK K (K ≥ 17), the first K ternary digits of 2^r are all 0 or 1 (no digit 2). But 2^r has roughly 0.63r ternary digits total. For r ≥ uK 13 ≈ 10^6, this is roughly 630,000 digits. The probability that all 630,000 digits are 0 or 1 is (2/3)^{630000} ≈ 10^{-110000}, essentially 0.

### Rigorous approach

**Lemma to prove:** For K ≥ 17 and r ∈ computeNK K with r ≥ uK 13 and r ≠ 0,2,8:
- 2^r has at least one digit 2 in positions K..K+49

**Proof strategy:**
1. 2^r = 3^K · q + c where c = 2^r mod 3^K is Cantor-like (first K digits 0/1)
2. q = (2^r - c) / 3^K ≥ 2^{uK 13} / 3^K - 1 (very large for K ≥ 17)
3. The ternary digits of 2^r at positions K..K+49 are the first 50 digits of q
4. Show q has digit 2 in its first 50 ternary digits

**Key number-theoretic facts:**
- The Cantor set in [0, 3^M) has 2^M elements, density (2/3)^M
- For M=50: density ≈ 10^{-9}
- The sequence 2^r mod 3^K is equidistributed (Weyl's theorem)
- The set of r where q is also Cantor-like has density 0

**Formalization approach:**
1. Prove density bound: among numbers in [N, N+L), at most L·(2/3)^M + O(1) are Cantor-like with M digits
2. Apply to q range: q ∈ [q_min, q_max) where q_min ≈ 2^{uK 13}/3^K
3. Show q cannot be Cantor-like for any r in the range

### Alternative: Computational extension

If number-theoretic approach is too complex, extend native_decide to K=17:
- uK 17 = 2·3^16 ≈ 86M elements
- Compute NK_17 and verify all r ≠ 0,2,8 have digit 2
- This pushes axiom to K ≥ 18

---

## Completed Milestones

1. ✅ Pure combinatorics layer (Narkiewicz, SayeLemma)
2. ✅ Ostrowski representation (Ostrowski.lean)
3. ✅ Lemma A / Q recurrence (OstrowskiFormLemma.lean)
4. ✅ CF theory for log₃(2) (ContinuedFraction/Log3.lean)
5. ✅ Bridge computations K=5..9 (BridgeCompute.lean)
6. ✅ Bridge computations r=48..1000 (BridgeComputeExtended.lean)
7. ✅ Full bridge chain (Bridge*.lean → OstrowskiAvoid.lean)
8. ✅ Rotation decomposition framework (RotationDecomp.lean)
9. ✅ CF stream characterization (log3_2_cf_stream)
10. ✅ Eliminate `ostrowski_invariant_structured` axiom (DisplacementInterface.lean)
11. ✅ Prove NK_mono (BridgeUniform.lean) — monotonicity of computeNK
12. ✅ K=13 bridge (BridgeK13.lean — List Nat candidates + native_decide)
13. ✅ K=14 bridge (BridgeK14.lean — Array Nat candidates + native_decide)
14. ✅ K=15 bridge (BridgeK15.lean — Array Nat candidates + native_decide)
15. ✅ K=16 bridge (BridgeMiddle16.lean — NK_16 List + native_decide)
16. ✅ K=13-16 candidate arrays (BridgeCandidates.lean)
17. ✅ Remove 4 dead axioms from Bridge.lean
18. ⬜ **Eliminate `ostrowski_invariant` axiom** ← **YOU ARE HERE**
19. ⬜ Final theorem assembly
