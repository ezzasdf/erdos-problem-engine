# The Erdős Ternary Conjecture & Cantor Multiplier Intersections

[![Lean 4.12.0](https://img.shields.io/badge/Lean-4.12.0-blue.svg)](https://github.com/leanprover/lean4)
[![Mathlib 4](https://img.shields.io/badge/Mathlib-v4.12.0-green.svg)](https://github.com/leanprover-community/mathlib4/tree/809c3fb3b5c8)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-yellow.svg)](LICENSE)

**Author:** Ezzeldin Ashraf Mohamed Shafey Wahba  
**Email:** [ezzeldinashraf.web@gmail.com](mailto:ezzeldinashraf.web@gmail.com)  
**Repository:** [https://github.com/ezzasdf/erdos-problem-engine](https://github.com/ezzasdf/erdos-problem-engine)

---

## Overview

This repository contains the complete interactive Lean 4 formalizations, computational certificates, and AMS-LaTeX research papers investigating:
1. **The Erdős Ternary Digit Conjecture (1978):** Reducing the classical question of powers of 2 omitting digit 2 in base 3 to a machine-verified Diophantine target via base-4 repunit 3-adic dynamics, rooted tree isomorphisms, and obstruction analysis.
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
        ├── BridgeCandidates.lean       # Finite-window candidate certificates ($K=13..16$)
        ├── BridgeCompute.lean          # Reflexive decision procedure proofs
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
```

---

## Axiom Audit

All core theoretical modules in this repository are **100% pure foundational**, depending exclusively on standard Lean core axioms:
- `propext` (Propositional Extensionality)
- `Classical.choice` (Axiom of Choice)
- `Quot.sound` (Quotient Soundness)

There is **zero reliance** on `sorryAx` / `sorry` or unverified axioms anywhere in the proofs.

Finite combinatorial certificates (in `BridgeCandidates.lean` for the First-Period Bridge, and `Lemma41Finite.lean` for $C(1, M)$ bounds) utilize standard reflexive kernel evaluation (`native_decide` / `Lean.ofReduceBool`), fully quarantined from the pure foundational modules.

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
