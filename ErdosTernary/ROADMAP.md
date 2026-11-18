# Erdos Ternary & Cantor Multiplier Formalization Roadmap

**Last updated:** November 2026  
**Lean version:** `leanprover/lean4:v4.12.0`  
**Mathlib commit:** `809c3fb3b5c8f5d7dace56e200b426187516535a`  
**Build command:** `lake build`

---

## 1. Formalization Status Table

### A. Cantor Multiplier Hausdorff Dimension Program (New in Nov 2026)

| Module | Mathematical Purpose | Status | Sorries | Axioms |
|---|---|:---:|:---:|:---:|
| `TimeReversal.lean` | Time-Reversal Duality $P M_{(a,b)} P = M_{(b-a,b)}^T$, charpoly equality, Boundary Case 2 reduction | **Kernel-verified** | 0 | 0 (standard: propext, choice, Quot.sound) |
| `CantorMultiplier.lean` | Universal Hausdorff dimension bound $\dim_H \le \log_3 \phi$, Attainer Families 1 & 2 exact equality, safe class classification | **Complete** | 0 | 0 (modular hypothesis `h_gap` for interior) |
| `Lemma41.lean` | Chain SFT recurrence $N(n+1) \le N(n) + N(n-1)$, Perron polynomial roots, Boundary Case 1 strict slack | **Complete** | 0 | 0 |
| `Lemma41Finite.lean` | Finite certificate definitions, Domino Chain combinatorics, finite verification predicates | **Complete** | 0 | 0 |

### B. Classical Erdős Conjecture & Bridge Theorem Program

| Module | Mathematical Purpose | Status | Sorries | Axioms |
|---|---|:---:|:---:|:---:|
| `Narkiewicz.lean` | Cantor set counting bound $N(x) \le 4 x^{\log_3 2}$ | Complete | 0 | 0 |
| `NarkiewiczBound.lean` | Extended Narkiewicz bounds | Complete | 0 | 0 |
| `SayeLemma.lean` | Saye's Lemma & $2^K$ branching factor bound | Complete | 0 | 0 |
| `LagariasHausdorff.lean` | Level-1 Hausdorff dimension $\dim_H C(1, 2) = \log_3 2$ | Complete | 0 | 0 |
| `Ostrowski.lean` | Ostrowski numeration system representation | Complete | 0 | 0 |
| `OstrowskiFormLemma.lean` | Mass-1 characterization lemma | Complete | 0 | 0 |
| `ContinuedFraction/Log3.lean` | $\log_3 2$ continued fraction, irrationality proof | Complete | 0 | 0 |
| `RotationDecomp.lean` | CF rotation decomposition | Complete | 0 | 0 |
| `BridgeCompute.lean` | Bridge theorem $K = 5..9$ via `native_decide` | Complete | 0 | 0 |
| `BridgeComputeExtended.lean` | Bridge candidates $r = 48..1000$ | Complete | 0 | 0 |
| `BridgeMiddle.lean` | Middle-digit bridge $K = 10..12$ | Complete | 0 | 0 |
| `BridgeK13.lean` | Level $K = 13$ candidate elimination | Complete | 0 | 0 |
| `BridgeK14.lean` | Level $K = 14$ candidate elimination | Complete | 0 | 0 |
| `BridgeK15.lean` | Level $K = 15$ candidate elimination | Complete | 0 | 0 |
| `BridgeMiddle16.lean` | Level $K = 16$ candidate elimination | Complete | 0 | 0 |
| `BridgeCandidates.lean` | Candidate arrays for $K = 13..16$ | Complete | 0 | 0 |
| `Mass1Dynamics.lean` | Mass-1 residue dynamics; no mass-1 for $K \ge 8$ | Complete | 0 | 0 |
| `DisplacementInterface.lean` | Structured displacement interface | Complete | 0 | 0 |
| `BridgeUniform.lean` | Uniform bridge theorem across all levels | Conditional | 0 | 1 (`ostrowski_invariant`) |

---

## 2. Dependency Architecture

### Multiplier Dimension Architecture (November 2026 Core)
```
Lemma41Finite.lean
       ↓
Lemma41.lean (Chain SFT recurrence & Boundary Case 1 slack)
       ↓
TimeReversal.lean (Time-Reversal Matrix Duality P M P = Mᵀ)
       ↓
CantorMultiplier.lean (Universal dimension bound & classification)
```

### Classical Erdős Program Architecture
```
Narkiewicz, SayeLemma          ← Pure combinatorics (complete)
        ↓
Ostrowski                      ← Ostrowski representation theorem (complete)
        ↓
OstrowskiFormLemma             ← Q recurrence, gd, topIdx, Al32 (complete)
        ↓
ContinuedFraction/Log3         ← log₃(2) CF bounds, irrationality (complete)
        ↓
RotationDecomp.lean            ← CF↔Al32 bridge (sorry-free)
        ↓
BridgeCompute → BridgeMiddle → BridgeUniform → BridgeOstrowski
   (K=5..9)    (K=10..12)     (K≥13 axiom)
        ↓
BridgeK13/K14/K15/K16
        ↓
Mass1Dynamics (no mass-1 residues for K ≥ 8)
```

---

## 3. Lean Kernel Axiom Audit (`TimeReversal.lean`)

Verified on remote server environment (`main-control`, 100.97.146.20) running Lean 4.12.0:
```text
✔ [1257/1257] Built ErdosTernary.TimeReversal

'ErdosTernary.TimeReversal.rev_rev' depends on axioms: [propext, Quot.sound]
'ErdosTernary.TimeReversal.isShift_rev_iff' depends on axioms: [propext, Quot.sound]
'ErdosTernary.TimeReversal.validCons_comm' depends on axioms: [propext, Quot.sound]
'ErdosTernary.TimeReversal.time_reversal_transition_duality' depends on axioms: [propext, Quot.sound]
'ErdosTernary.TimeReversal.boundary_case2_reversal_to_boundary_case1' depends on axioms: [propext, Quot.sound]
'ErdosTernary.TimeReversal.charmatrix_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosTernary.TimeReversal.charpoly_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosTernary.TimeReversal.time_reversal_matrix_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosTernary.TimeReversal.charpoly_time_reversal_invariance' depends on axioms: [propext, Classical.choice, Quot.sound]
'ErdosTernary.TimeReversal.boundary_case2_charpoly_eq_boundary_case1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`sorryAx`:** **0**
- **Custom / Ad-hoc axioms:** **0**
- **`native_decide`:** **0**

---

## 4. Next Formalization Objectives

1. **Mathlib SFT Ergodic Infrastructure (`h_gap` Discharging):**
   - Formalize the Perron–Frobenius theorem for primitive non-negative matrices (`Matrix.IsPrimitive M → ∃ v > 0, M v = λ v`).
   - Construct the Parry Markov measure on shift spaces.
   - Formalize Birkhoff's ergodic theorem for cylinder counts to discharge `h_gap` unconditionally in Lean.

2. **Erdős Beyond First Period ($K \ge 17$):**
   - Discharge `ostrowski_invariant` by formalizing the connection between large Ostrowski coefficients ($b_k \ge 1$ for $k \ge 5$) and irrational rotation avoidance of the Cantor cylinder set $C_{30}$.
