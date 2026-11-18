# Erdős Ternary & Cantor Multiplier Dimension Program — Master Roadmap

**Last Updated:** November 2026  
**Repository:** [https://github.com/ezzasdf/erdos-problem-engine](https://github.com/ezzasdf/erdos-problem-engine)  
**Active Branches:** `main`, `audit/erdos-proof` (both synchronized at commit `118e596`)

---

## 1. Executive Summary & Program Scope

This project encompasses two interrelated mathematical programs centered on the geometry and dynamics of ternary expansions and the middle-third Cantor set $C = \{ \sum_{i=1}^\infty d_i 3^{-i} : d_i \in \{0, 1\} \}$:

1. **The Classical Erdős Ternary Conjecture (1978):**
   - *Problem:* Show that $2^0 = 1, 2^2 = 4, 2^8 = 256$ are the only powers of 2 omitting digit 2 in base 3.
   - *Status:* Verified computationally to $n \le 8.1 \times 10^{18}$ (second-deepest known). Bridge Theorem (first period) formal proof completed in Lean 4 for $K = 5..16$.

2. **The Cantor Multiplier Hausdorff Dimension Program (Lagarias 2009 / Ours 2026):**
   - *Problem:* Determine the Hausdorff dimension $\dim_H C(1, M)$ of intersection sets $C(1, M) = C \cap M^{-1}(C)$ for integer multipliers $M$, classify all extremizers achieving the golden ratio bound $\log_3 \phi \approx 0.4380$, and resolve Lagarias's multiplier conjectures.
   - *Status:* **Complete in mathematical prose; Lean-verified core with Time-Reversal Duality (November 2026).** Universal upper bound $\dim_H C(1, M) \le \log_3 \phi$ and exact extremizer iff classification fully established.

---

## 2. Comprehensive Status Map

| Mathematical Result | Domain | Prose Status | Lean 4 Status | Primary File(s) |
|---|---|:---:|:---:|---|
| **Universal Dimension Bound** $\dim_H C(1, M) \le \log_3 \phi$ | All safe $M$ ($3^b - 3^a + 1$, $3^a + 1$) | Proved [P] | **100% Lean-verified** (0 sorry, 0 custom axioms) | `Lemma41.lean`, `CantorMultiplier.lean` |
| **Attainer Family 1** ($M = 3^a + 1$) | Exact equality $\dim_H = \log_3 \phi$ | Proved [P] | **100% Lean-verified** (0 sorry, 0 custom axioms) | `CantorMultiplier.lean` |
| **Attainer Family 2** ($M = 3^{2a} - 3^a + 1$) | Exact equality $\dim_H = \log_3 \phi$ | Proved [P] | **100% Lean-verified** (0 sorry, 0 custom axioms) | `CantorMultiplier.lean` |
| **Boundary Case 1** ($a = 1, b \ge 3$) | Strict slack $\lambda(1, b) < \phi$ | Proved [P] | **100% Lean-verified** (0 sorry, 0 custom axioms) | `Lemma41.lean` (`perronPoly_at_phi_pos`) |
| **Time-Reversal Duality Theorem** | $P M_{(a, b)} P = M_{(b-a, b)}^T$ | Proved [P] | **100% Lean-verified** (0 sorry, 0 custom axioms) | `TimeReversal.lean` |
| **Boundary Case 2** ($b - a = 1, a \ge 2$) | Reduction $\lambda(a, a+1) = \lambda(1, a+1) < \phi$ | Proved [P] | **100% Lean-verified** (0 sorry, 0 custom axioms) | `TimeReversal.lean` |
| **Non-Extremizer Interior** ($a \ge 2, b - a \ge 2$) | Universal $2b$-periodic orbit + Parry measure | Proved [P] | Modular interface `h_gap` (PF + Parry measure) | `submission_draft.md` §2.5, `CantorMultiplier.lean` |
| **Saye's Lemma & Branching Bound** | $2^K$ branching structure | Proved [P] | **100% Lean-verified** (0 sorry) | `SayeLemma.lean` |
| **Narkiewicz Counting Bound** | $N(x) \le 4 x^{\log_3 2}$ | Proved [P] | **100% Lean-verified** (0 sorry) | `Narkiewicz.lean`, `NarkiewiczBound.lean` |
| **Lagarias Level-1 Dimension** | $\dim_H C(1, 2) = \log_3 2$ | Proved [P] | **100% Lean-verified** (0 sorry) | `LagariasHausdorff.lean` |
| **Bridge Theorem (First Period)** | $n \in [0, u_K) \cap B_K \cap A_L = \{0, 2, 8\}$ | Proved [P] | **100% Lean-verified** for $K = 5..16$ | `BridgeCompute.lean`, `BridgeMiddle.lean`, `BridgeCandidates.lean` |
| **Mass-1 Dynamics Exclusion** | No mass-1 residues for $K \ge 8$ | Proved [P] | **100% Lean-verified** (0 sorry, 0 axioms) | `Mass1Dynamics.lean` |

---

## 3. Major Breakthroughs (November 2026)

### Breakthrough 1: Time-Reversal Duality Theorem
*Theorem:* Let $1 \le a < b$ and let $M_{(a, b)}$ be the $2^b \times 2^b$ transfer matrix of the chain SFT $\Sigma_{(a, b)}$. Let $P$ be the permutation matrix of the bit-reversal involution on $\{0, 1\}^b$: $(P u)_j = u_{b-1-j}$. Then:
$$P M_{(a, b)} P = M_{(b-a, b)}^T.$$
*Consequence:* $\det(x I - M_{(b-a, b)}) = \det(x I - M_{(a, b)})$ identically, establishing **$\lambda(a, b) = \lambda(b-a, b)$**.
- Completely resolves **Boundary Case 2** ($b - a = 1$): maps bijectively to Boundary Case 1 ($a = 1$), yielding $\lambda(a, a+1) = \lambda(1, a+1) < \phi$.
- Kernel-verified in Lean 4 without custom axioms in `ErdosTernary/TimeReversal.lean`.

### Breakthrough 2: Universal $2b$-Periodic Orbit for Step B.2
To prove $\mu([w_*]) > 0$ on the interior domain without case splits:
- The alternating sequence $z_i = \mathbf{1}_{(i \bmod 2b) \ge b}$ satisfies $z_{i-b} = 1 - z_i$, so:
  $$z_i - z_{i-a} + z_{i-b} = 1 - z_{i-a} \in \{0, 1\} \subset [0, 1]$$
  identically on $\mathbb{Z}$ for all $1 \le a < b$.
- The sequence embeds both witness types ($w_* = 0^{b-1} 1 1$ for $g \ge 2$, $w_* = 0^b 1$ for $g = 1$) into the maximal recurrent component $R$, completing the Parry measure positive cylinder density step $\mu([w_*]) = \varepsilon(a, b) > 0$.

### Breakthrough 3: Lean 4 Kernel Certification on Remote Environment
- Assembled and compiled pinned Mathlib 4.12.0 oleans on remote servers (`main-control`, 100.97.146.20).
- Lake build: `✔ [1257/1257] Built ErdosTernary.TimeReversal`.
- `#print axioms` audit: all declarations certified with strictly standard axioms (`[propext, Classical.choice, Quot.sound]`), 0 `sorry`, 0 `native_decide`.

---

## 4. Completed Work Packages (Phases 1–11)

- **Phase 1: Saye's Algorithm Implementation (DONE):** Rust engine verifying $n \le 8.1 \times 10^{18}$ (`verify_erdos_rs`).
- **Phase 2: Saye's Lemma Formalization (DONE):** Formalized in Lean 4 (`SayeLemma.lean`, 0 sorry).
- **Phase 3: Narkiewicz Bound (DONE):** Cantor set counting bound formalized (`Narkiewicz.lean`, 0 sorry).
- **Phase 4: Lagarias Level-1 Hausdorff Dimension (DONE):** $\dim_H = \log_3 2$ formalized (`LagariasHausdorff.lean`).
- **Phase 5: First-Period Bridge Theorem (DONE):** Fully formalized for $K = 5..9$ (`BridgeCompute.lean`) and $K = 10..12$ (`BridgeMiddle.lean`).
- **Phase 6: High-Level Bridge Extensions (DONE):** Candidate array generation and verification for $K = 13..16$ (`BridgeCandidates.lean`, `BridgeMiddle16.lean`).
- **Phase 7: Mass-1 Dynamics & Displacement Interface (DONE):** Proved no mass-1 residues exist for $K \ge 8$; eliminated structural axioms (`Mass1Dynamics.lean`, `DisplacementInterface.lean`).
- **Phase 8: Ostrowski Numeration & Irrational Rotation (DONE):** Continued fractions for $\log_3 2$, irrationality proof, and rotation decomposition (`ContinuedFraction/Log3.lean`, `RotationDecomp.lean`).
- **Phase 9: Multiplier Chain SFT Recurrence (DONE):** Fibonacci upper bound $N(n+1) \le N(n) + N(n-1)$ formalized in Lean 4 (`Lemma41.lean`, `Lemma41Finite.lean`).
- **Phase 10: Multiplier Dimension Classification (DONE):** Universal upper bound and attainer classification formalized (`CantorMultiplier.lean`).
- **Phase 11: Time-Reversal Duality & Boundary Case 2 (DONE):** Matrix transpose duality and spectral invariance kernel-verified (`TimeReversal.lean`).

---

## 5. Next Steps & Open Work

### Track A: Publication of Multiplier Dimension Paper
- [x] Complete technical paper draft (`paper/cantor_multiplier_dimension.md`).
- [x] Synchronize verification logs (`paper/phase3_bridge_report.md`).
- [x] Integrate backing Python verification suite (`scripts/cantor_multiplier/`).
- [ ] Prepare preprint submission for arXiv / journal submission.

### Track B: Formalization of General SFT Ergodic Theory (`h_gap`)
Discharging `h_gap` unconditionally in Lean 4 represents a general Mathlib formalization project:
1. **Perron–Frobenius Theorem:** Formalize existence and uniqueness of positive eigenvectors for primitive matrices (`IsPrimitive M → ∃ v > 0, M v = λ v`).
2. **Parry Markov Measure:** Formalize construction of the measure of maximal entropy on shifts of finite type.
3. **Birkhoff Ergodic Theorem for SFT Cylinders:** Formalize asymptotic cylinder density convergence.
4. **Orbit Recurrence:** Formalize embedding of the universal $2b$-periodic orbit into the recurrent component.

### Track C: Erdős Conjecture Beyond First Period ($K \ge 17$)
- Bridge theorem covers first period $[0, u_K)$. Extending to all $n$ requires connecting the Ostrowski numeration of large survivors to the irrational rotation avoidance of the Cantor cylinder set.
- Formalize Ostrowski coefficient bounds for large $r \ge u_K(13)$ forcing leading-digit 2.

---

## 6. Repository Layout & Artifact Map

```
.
├── ErdosTernary/
│   ├── ErdosTernary.lean                  # Package entry point
│   ├── ErdosTernary/
│   │   ├── TimeReversal.lean              # Time-Reversal Duality (100% Lean-verified)
│   │   ├── CantorMultiplier.lean          # Hausdorff dimension & attainer theorems
│   │   ├── Lemma41.lean                   # Bulk recurrence & Perron polynomial slack
│   │   ├── Lemma41Finite.lean             # SFT certificate definitions
│   │   ├── SayeLemma.lean                 # Saye's Lemma (0 sorry)
│   │   ├── Narkiewicz.lean                # Narkiewicz counting bound (0 sorry)
│   │   ├── LagariasHausdorff.lean         # Level-1 Hausdorff dimension (0 sorry)
│   │   ├── Mass1Dynamics.lean             # Mass-1 residue exclusion (0 sorry)
│   │   ├── RotationDecomp.lean            # CF rotation decomposition
│   │   └── Bridge*.lean                   # Bridge theorem levels K=5..16
├── paper/
│   ├── cantor_multiplier_dimension.md     # Full submission draft paper
│   ├── phase3_bridge_report.md            # Kernel audit and session log
│   ├── draft.md                           # Original Erdős powers-of-2 draft
│   └── ostrowski_bridge.md                # Ostrowski bridge writeup
└── scripts/
    └── cantor_multiplier/                 # Computational verification suite (Python)
        ├── lemma41_transfer.py            # Transfer matrix certificate checker
        ├── x2p_third_family.py            # Exact Perron polynomial factorizer
        ├── x2p_dim_table.py               # Exact Hausdorff dimension table generator
        └── lemma41_tii_proof.py           # Combinatorial certificate validator
```
