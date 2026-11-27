# The Erdős Ternary Conjecture & Cantor Multiplier Intersections

[![CI](https://github.com/ezzasdf/erdos-problem-engine/actions/workflows/verify.yml/badge.svg)](https://github.com/ezzasdf/erdos-problem-engine/actions/workflows/verify.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24595631.svg)](https://doi.org/10.5281/zenodo.24595631)
[![Lean 4.12.0](https://img.shields.io/badge/Lean-4.12.0-blue.svg)](https://github.com/leanprover/lean4)
[![Mathlib 4](https://img.shields.io/badge/Mathlib-v4.12.0-green.svg)](https://github.com/leanprover-community/mathlib4/tree/809c3fb3b5c8)
[![License: PolyForm Strict 1.0.0](https://img.shields.io/badge/License-PolyForm%20Strict%201.0.0-orange.svg)](LICENSE-CODE) [![Commercial license](https://img.shields.io/badge/Commercial-license%20required-red.svg)](COMMERCIAL.md)

**Author:** Ezzeldin Ashraf Mohamed Shafey Wahba  
**Email:** [ezzeldinashraf.web@gmail.com](mailto:ezzeldinashraf.web@gmail.com)  
**Repository:** [https://github.com/ezzasdf/erdos-problem-engine](https://github.com/ezzasdf/erdos-problem-engine)

---

## Overview

This repository contains the complete interactive Lean 4 formalizations, computational certificates, and AMS-LaTeX research papers investigating:
1. **The Erdős Ternary Digit Conjecture (1979):** Reducing the classical question of powers of 2 omitting digit 2 in base 3 (posed by Paul Erdős in *Mathematics Magazine*, 1979) to a machine-verified Diophantine target via base-4 repunit 3-adic dynamics, rooted tree isomorphisms, and obstruction analysis.
2. **The Extremal Hausdorff Dimension of Cantor Multiplier Intersections:** A classification of Hausdorff dimensions $\dim_H C(1, M) = \dim_H (\Sigma \cap M^{-1} \Sigma)$ for digitwise-safe multipliers, discovering a second infinite family of Golden Mean Shift extremizers attaining $\log_3 \phi \approx 0.438018$, with a formalized Time-Reversal Duality.

---

## Research Papers (`paper/`)

Both papers are fully typeset in AMS-LaTeX (`amsart`) with exact BibTeX bibliographies (`paper/references.bib`) and zero overfull/underfull box warnings:

- **Paper 1: Multiplier Intersections & Extremal Dimension**  
  *The Extremal Hausdorff Dimension of Cantor Multiplier Intersections and the Golden Mean Shift*  
  - Source: [`paper/cantor_multiplier_dimension.tex`](paper/cantor_multiplier_dimension.tex)  
  - PDF: [`paper/cantor_multiplier_dimension.pdf`](paper/cantor_multiplier_dimension.pdf)
- **Paper 2: The Erdős Conjecture Reduction & Obstructions**  
  *The Erdős Ternary Digit Conjecture: Rooted Repunit Trees, 3-Adic Dynamics, Archimedean Decoupling, and the Negative-Power Duality*  
  - Source: [`paper/erdos_ternary_repunit.tex`](paper/erdos_ternary_repunit.tex)  
  - PDF: [`paper/erdos_ternary_repunit.pdf`](paper/erdos_ternary_repunit.pdf)
- **Bibliography:** [`paper/references.bib`](paper/references.bib)

---

## Lean 4 Project Structure

The root Lean 4 package is located in the [`ErdosTernary/`](ErdosTernary/) directory:

```text
erdos-problem-engine/
├── README.md                      # Project documentation and build guide
├── paper/                         # AMS-LaTeX papers, bibliography, and compiled PDFs
│   ├── cantor_multiplier_dimension.tex
│   ├── cantor_multiplier_dimension.pdf
│   ├── erdos_ternary_repunit.tex
│   ├── erdos_ternary_repunit.pdf
│   └── references.bib
└── ErdosTernary/                  # Root Lean 4 package directory
    ├── lakefile.lean              # Lake package configuration
    ├── lean-toolchain             # Pinned: leanprover/lean4:v4.12.0
    ├── lake-manifest.json         # Pinned Mathlib commit 809c3fb3b5c8
    └── ErdosTernary/              # Lean source modules
        ├── RepunitBase4.lean           # $4^s = 3 R_s(4) + 1$ & digit shift
        ├── RepunitLifting.lean         # Modular lifting & exact 2-of-3 branching
        ├── RepunitTreeIso.lean         # Rooted Tree Isomorphism $\mathcal{T}_{\mathrm{rep}} \cong \mathcal{T}_{\mathrm{pow}}$
        ├── RepunitArchimedean.lean     # Archimedean–3-Adic Decoupling Theorem
        ├── RepunitDiophantine.lean     # Equivalence: Erdős ⟺ jointSurvivors = ∅
        ├── RepunitCarryPacket.lean     # Mod-8 non-recurrence of carry packets
        ├── NegativePower.lean          # Negative-power theorem & mod-8 Gap Lemma
        ├── RepunitCarryConnection.lean # Carry automaton ≅ SFT $C(1, 4)$ isomorphism
        ├── Bridge.lean                 # Trailing filter $B_K$ & leading filter $A_L$
        ├── BridgeCompute.lean          # Leading-digit deciders ($K=5..9$) & low-50 evaluators
        ├── BridgeMiddle.lean           # Middle digit window $[K, 50)$ certificates ($K=10..12$)
        ├── BridgeMiddle16.lean         # Middle window certificates for higher scales
        ├── BridgeCandidates.lean       # Filtered modular residue candidates
        ├── BridgeK13.lean..BridgeK17.lean # Finite candidate verification (K=13..17)
        ├── BridgeK18.lean              # Period u_18 = 258,280,326 certificate aggregator
        ├── BridgeK18Part1.lean..Part3.lean # 162 chunk certificates for K=18
        ├── BridgeCantorChunked.lean    # Chunked parallel range-checking framework
        ├── BridgeCantorChunkedProofs.lean # Range-chunked certificates (K=15..17)
        ├── BridgeUniform.lean          # First-period bridge verification (5 ≤ K ≤ 18)
        ├── BridgeOstrowskiInvariant.lean # Re-export of verified iff theorem & asymptotic axiom
        ├── CantorMultiplier.lean       # Safe multipliers & Golden Mean shift bound
        ├── TimeReversal.lean           # Matrix similarity $P M_{(a,b)} P = M_{(b-a,b)}^T$
        ├── PeriodicOrbit.lean          # Recurrent component primitivity & $2b$-periodic orbit
        └── Lemma41Finite.lean          # 957 finite-window certificates for $C(1, M)$
```

---

## Reproducible Build & Verification Instructions

### 1. Prerequisites
Install `elan` (the official Lean toolchain manager):
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source ~/.elan/env
```

### 2. Fetch Mathlib Cache & Build
Navigate to the root Lean package directory:
```bash
cd ErdosTernary

# Download precompiled Mathlib olean cache for commit 809c3fb3b5c8
lake exe cache get

# Compile all modules and verify all proofs
lake build
```

### 3. Verifying Individual Modules
You can verify any individual module with `lake env lean`:
```bash
# Verify the Diophantine reduction of the Erdős Conjecture:
lake env lean ErdosTernary/RepunitDiophantine.lean

# Verify the Negative-Power Theorem and Gap Lemma:
lake env lean ErdosTernary/NegativePower.lean

# Verify the Rooted Tree Isomorphism:
lake env lean ErdosTernary/RepunitTreeIso.lean

# Verify the Time-Reversal Duality Theorem:
lake env lean ErdosTernary/TimeReversal.lean

# Verify the First-Period Bridge Theorem:
lake env lean ErdosTernary/BridgeUniform.lean
```

---

## Trust Model & Axiom Audit

We maintain a strict distinction between foundational mathematical proofs and computational decision procedures:

### 1. Foundational Kernel Theorems (TCB = Lean 4 Kernel)
All core theoretical modules (`RepunitBase4.lean` through `RepunitCarryConnection.lean`) are **100% pure foundational**. They are checked strictly by the Lean 4 kernel, depending exclusively on standard foundation axioms:
- `propext` (Propositional Extensionality)
- `Classical.choice` (Axiom of Choice)
- `Quot.sound` (Quotient Soundness)

There is **zero reliance** on `sorryAx` / `sorry`, unverified axioms, or decision procedure oracles in these theorems.

### 2. Computational Certificates (TCB Extended to Lean Compiler/VM)
Finite combinatorial certificates (such as the First-Period Bridge certificates in `BridgeCompute.lean`, `BridgeMiddle.lean`, `BridgeK13.lean`–`BridgeK18.lean`, `BridgeCantorChunkedProofs.lean`, and `Lemma41Finite.lean`) use `native_decide` and `Lean.ofReduceBool`. 
- `native_decide` compiles Lean deciders to native executable bytecode and runs them within the Lean runtime environment.
- This extends the Trusted Computing Base (TCB) beyond the foundational Lean kernel to include the Lean compiler and C++ runtime evaluator, enabling verified exhaustive search over candidate sets with period $u_K \le 258,280,326$ ($5 \le K \le 18$).
- For $K \in \{5, \dots, 9\}$, the witness digit 2 is verified within the leading 30 digits (`hasLeadingDigit2`).
- For $K \in \{10, 11, 12\}$, the witness digit 2 is verified within the middle window $[K, 50)$ modulo $3^{50}$.
- For $K \in \{13, \dots, 18\}$, the witness digit 2 is verified within the lowest 50 digits modulo $3^{50}$.
- The open asymptotic conjecture for $K > 18$ is quarantined in `BridgeUniform.lean` and `BridgeOstrowskiInvariant.lean` under an explicit hypothesis (`axiom ostrowski_invariant`), ensuring the verified finite theorem for $K \le 18$ depends on zero unproved axioms.

---

## Citation

If you use these formalizations, proofs, or results in your research, please cite:

```bibtex
@article{Wahba2026Erdos,
  author    = {Ezzeldin Ashraf Mohamed Shafey Wahba},
  title     = {The {E}rd{\H{o}}s Ternary Digit Conjecture: Rooted Repunit Trees, 3-Adic Dynamics, Archimedean Decoupling, and the Negative-Power Duality},
  journal   = {Preprint},
  year      = {2026},
  howpublished = {\url{https://github.com/ezzasdf/erdos-problem-engine}}
}

@article{Wahba2026Cantor,
  author    = {Ezzeldin Ashraf Mohamed Shafey Wahba},
  title     = {The Extremal Hausdorff Dimension of Cantor Multiplier Intersections and the Golden Mean Shift},
  journal   = {Preprint},
  year      = {2026},
  howpublished = {\url{https://github.com/ezzasdf/erdos-problem-engine}}
}
```
