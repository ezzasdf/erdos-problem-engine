#!/usr/bin/env python3
"""
Generates the 1-Page Commercial Demonstration Deck:
'Decoupled High-Assurance Verification for Discrete Dynamical Systems'
Outputs:
  - COMMERCIAL_DEMO_DECK.pdf (Clean A4 Executive PDF via PyMuPDF)
  - COMMERCIAL_DEMO_DECK.md (Standard GitHub Flavored Markdown)
"""

import sys
from pathlib import Path
import fitz  # PyMuPDF

REPO_ROOT = Path(__file__).resolve().parent.parent

MD_CONTENT = """# Decoupled High-Assurance Verification for Discrete Dynamical Systems
## Erdős Mathematical Verification Engine (EMVE) — Executive Technical Brief

**Author:** Ezzeldin Ashraf Mohamed Shafey Wahba (`ezzeldinashraf.web@gmail.com`)  
**Zenodo DOI:** [10.5281/zenodo.24595631](https://doi.org/10.5281/zenodo.24595631) | **GitHub:** [github.com/ezzasdf/erdos-problem-engine](https://github.com/ezzasdf/erdos-problem-engine)  
**Release Version:** `emve-cert-v1.0.0` | **Status:** Technical Preview / Evaluation Kit  

---

### 1. The Challenge: Numerical Uncertainty in Discrete Transition Spectra
Verification pipelines for discrete dynamical systems, carry automata, and state-transition graphs frequently evaluate spectral radius bounds $\\rho(A) \\le \\lambda^*$ to guarantee contractivity, safety invariants, or dimension bounds. Standard numerical packages rely on floating-point eigensolvers (e.g., LAPACK/BLAS). In borderline or ill-conditioned cases, floating-point methods can introduce numerical uncertainty and precision loss. EMVE offers an exact integer-based verification path for supported certificate forms, eliminating floating-point rounding error from the witness audit.

---

### 2. The Solution: Decoupled Proof-Carrying Certificate Architecture
EMVE decouples complex, heuristic state-space exploration from formal witness verification:
- **Heuristic / Combinatorial Exploration (Untrusted):** High-throughput search engines in Rust and Python discover extremal transition graphs and candidate Perron eigenvectors.
- **Integer Collatz–Wielandt Witnesses (Level 1 Verification):** To certify $\\rho(A) \\le 1.60 < \\varphi$, EMVE generates an integer witness vector $v \\in \\mathbb{Z}_{>0}^n$ and positive scaling integers $c, d$ satisfying $c \\cdot (A v) \\le d \\cdot v$ across all rows. Evaluated purely in arbitrary-precision integer arithmetic (zero floating-point operations).
- **Exact Sturm Root Counting:** For extremal equality ($\\rho(A) = \\varphi$), EMVE computes the characteristic polynomial, verifies $(x^2 - x - 1) \\mid P(x)$, and constructs an exact Sturm chain in $\\mathbb{Q}(\\sqrt{5})$ to certify 0 real roots exceed $\\varphi$.

---

### 3. Three-Level Verification Hierarchy & Trust Boundaries
To eliminate ambiguity, EMVE enforces explicit epistemic boundaries across three verification levels:
1. **Level 1 (Verified Certificate):** Standalone mathematical validation of the explicit matrix $A$. The supplied witness is checked in ~0.0002s via pure Python standard library or inside Lean 4's trusted kernel by definitional reflexivity (`by rfl`) with zero axioms (`[]`).
2. **Level 2 (Verified Derivation):** Confirms reproducibility from the project's canonical state-space generator (`get_graph_for_M`), verifying that matrix dimensions, family parameters, and lags match canonical derivation.
3. **Level 3 (Analytical Theorem):** The continuous Frostman measure bridge connecting symbolic growth rates $\\log_3 \\lambda_0$ to Hausdorff dimension on $\\mathbb{R}$ remains an analytical paper proof conditional on Hypothesis (H).

---

### 4. Measured Performance Benchmarks (AMD Ryzen 9 5950X, Linux 6.8)
All benchmarks were measured on a reference AMD Ryzen 9 5950X (16C/32T, 3.4 GHz base / 4.9 GHz boost, 64 GB DDR4 RAM, Ubuntu Linux kernel 6.8):
- **Standalone Auditor (`scripts/check_certificate.py`):** Evaluates $M=19$ ($6 \\times 6$ matrix) in **~0.0002 seconds** (mean over 100 runs, stock Python 3.12 standard library, zero external dependencies, SHA-256 payload integrity check).
- **23-Modulus Verified Catalog:** All 23 multipliers ($2 \\le M \\le 35, \\gcd(M, 3) = 1$) independently audited with 100% pass rate (19 Collatz–Wielandt bounds + 4 Sturm extremizers).
- **Standalone Lean 4 Module:** Compact Lean 4 file (`CertCheck.lean`, ~130 lines) verified in Lean 4 core (`Init`) without Mathlib, including **six negative regression theorems covering five failure categories** (ragged rows, dimension mismatches, non-positive witness entries, zero multipliers $c$ and $d$, and false inequalities).
- **Rust Exploration Engine (`verify_middle`):** Single-run timing of **0.32 seconds** across 16 threads (`cargo run --release`, evaluating $2.8 \\times 10^7$ candidate transitions across window $k=17$, yielding $\\approx 87.5$ million transitions/sec).
- **Python Sequential Scan (`verify_dimensions.py`):** Single-run timing of **29.1 seconds** sequentially generating graphs and certifying all 1,333 moduli $2 \\le M \\le 2000$ (`python3 scripts/cantor_multiplier/verify_dimensions.py --scan 2000`, Python 3.12, SymPy 1.14, yielding $\\approx 45.8$ certified moduli/sec).

---

### 5. Target Domains for Evaluation & Collaborative Pilot Roadmap
- **Target Applications for Evaluation:**
  - *Cryptographic Carry Circuits & SMT Pipelines:* Target domain for proving absence of carry-chain overflow without floating-point relaxation.
  - *Discrete Control Automata & State Machines:* Target domain for bounding transition matrix growth rates with deductive certainty.
  - *Interactive Theorem Prover Tactics:* Target domain for direct ingestion of integer witness vectors into Lean 4, Coq, and Isabelle/HOL.
- **Collaborative Pilot Framework:**
  - Structured 4-week technical evaluation to assess solver scalability, generate domain-specific witness certificates, and validate integration feasibility into client audit toolchains.
"""

def generate_pdf():
    doc = fitz.open()
    # A4 dimensions: 595.28 x 841.89 points
    page = doc.new_page(width=595.28, height=841.89)
    
    # Color palette
    NAVY = (0.08, 0.18, 0.36)
    DARK_GRAY = (0.15, 0.15, 0.15)
    LIGHT_BG = (0.96, 0.97, 0.99)
    ACCENT_BLUE = (0.12, 0.42, 0.78)
    BORDER_COLOR = (0.80, 0.85, 0.92)
    
    # 1. Header Banner
    page.draw_rect(fitz.Rect(30, 24, 565, 87), color=NAVY, fill=LIGHT_BG)
    page.insert_text((42, 44), "DECOUPLED HIGH-ASSURANCE VERIFICATION", fontsize=15, fontname="helv", color=NAVY)
    page.insert_text((42, 59), "FOR DISCRETE DYNAMICAL SYSTEMS & CARRY AUTOMATA", fontsize=11, fontname="helv", color=ACCENT_BLUE)
    page.insert_text((42, 74), "Erdős Mathematical Verification Engine (EMVE) — Executive Technical Brief (v1.0.0)", fontsize=8.5, fontname="helv", color=DARK_GRAY)
    page.insert_text((42, 83), "Author: Ezzeldin Ashraf | DOI: 10.5281/zenodo.24595631 | GitHub: github.com/ezzasdf/erdos-problem-engine", fontsize=7.5, fontname="helv", color=DARK_GRAY)

    y = 96

    def draw_section(title, lines, box_height):
        nonlocal y
        # Section Header
        page.draw_rect(fitz.Rect(30, y, 565, y + 15), color=ACCENT_BLUE, fill=NAVY)
        page.insert_text((38, y + 11), title.upper(), fontsize=8.5, fontname="helv", color=(1, 1, 1))
        y += 17
        
        # Content box
        rect = fitz.Rect(30, y, 565, y + box_height)
        page.draw_rect(rect, color=BORDER_COLOR, fill=LIGHT_BG)
        
        text_y = y + 11
        for line in lines:
            if isinstance(line, tuple):
                prefix, body = line
                page.insert_text((38, text_y), prefix, fontsize=7.2, fontname="helv", color=NAVY)
                prefix_width = fitz.get_text_length(prefix, fontname="helv", fontsize=7.2)
                page.insert_text((38 + prefix_width + 2, text_y), body, fontsize=7.2, fontname="helv", color=DARK_GRAY)
            else:
                page.insert_text((38, text_y), line, fontsize=7.2, fontname="helv", color=DARK_GRAY)
            text_y += 11.0
        y += box_height + 7

    # Section 1: The Problem
    draw_section(
        "1. The Core Challenge: Numerical Uncertainty in Discrete Spectral Bounds",
        [
            "• Modern verification of state-transition graphs and carry automata relies on spectral radius bounds: rho(A) <= lambda*.",
            "• Floating-point methods can introduce numerical uncertainty and precision loss in borderline or ill-conditioned cases.",
            "• EMVE offers an exact integer-based verification path for supported certificate forms, eliminating floating-point rounding errors."
        ],
        box_height=36
    )

    # Section 2: Decoupled Architecture
    draw_section(
        "2. The Solution: Decoupled Proof-Carrying Certificate Architecture",
        [
            ("• Exploration vs. Verification: ", "Untrusted search in Rust/Python discovers graphs; independent checker audits exact witnesses."),
            ("• Integer Collatz-Wielandt Witnesses: ", "Certifies rho(A) <= 1.60 < phi via integer inequality 5*(A@v) <= 8*v in pure Z arithmetic."),
            ("• Exact Sturm Sequence Root Counting: ", "Certifies extremal cases rho(A) = phi via exact charpoly factoring & Sturm chains in Q(sqrt5)."),
            ("• Zero Numerical Error: ", "Acceptance is evaluated purely in integer and algebraic arithmetic without floating-point approximations.")
        ],
        box_height=47
    )

    # Section 3: Three-Tier Hierarchy
    draw_section(
        "3. Three-Level Verification Hierarchy & Explicit Trust Boundaries",
        [
            ("• Level 1 (Verified Certificate): ", "Zero-trust verification of matrix A. Python stdlib audits in 0.0002s; Lean 4 audits via 'by rfl'."),
            ("• Level 2 (Verified Derivation): ", "Confirms exact reproducibility from EMVE's canonical state-space generator (get_graph_for_M)."),
            ("• Level 3 (Analytical Theorem): ", "Continuous Frostman bridge connecting symbolic growth to Hausdorff dimension on R (analytical proof).")
        ],
        box_height=36
    )

    # Section 4: Benchmarks & Catalog
    draw_section(
        "4. Measured Performance Benchmarks (AMD Ryzen 9 5950X, Linux 6.8)",
        [
            ("• Standalone Auditor (Python 3.12 stdlib): ", "M=19 (6x6 matrix) audited in ~0.0002s (mean over 100 runs, 0 external dependencies)."),
            ("• 23-Modulus Verified Catalog: ", "All 23 multipliers (2 <= M <= 35, gcd(M,3)=1) audited with 100% PASS rate (19 CW + 4 Sturm)."),
            ("• Lean 4 Core Module (~130 lines): ", "Verified in core Lean 4 (0 Mathlib); includes 6 negative regression theorems across 5 failure modes."),
            ("• Exploration Benchmarks (Single-run): ", "Rust cargo --release: 2.8e7 transitions in 0.32s (87.5M/s); Python --scan 2000: 1,333 moduli in 29.1s (45.8/s).")
        ],
        box_height=47
    )

    # Section 5: Target Domains & Pilot
    draw_section(
        "5. Target Evaluation Domains & Collaborative Pilot Roadmap",
        [
            ("• Cryptographic Carry Circuits: ", "Targeting formal certification of carry-propagation bounds without floating-point relaxation."),
            ("• Interactive Theorem Prover Tactics: ", "Targeting direct ingestion of integer witness vectors into Lean 4, Coq, and Isabelle/HOL."),
            ("• Discrete Control Automata: ", "Targeting high-assurance contractivity and stability verification of discrete transition matrices."),
            ("• Collaborative Pilot Framework: ", "Structured 4-week technical evaluation to assess solver scalability and toolchain integration.")
        ],
        box_height=47
    )

    # Footer
    page.draw_rect(fitz.Rect(30, 805, 565, 825), color=NAVY, fill=LIGHT_BG)
    page.insert_text((38, 818), "EMVE v1.0.0 | PolyForm Strict License | Zenodo DOI: 10.5281/zenodo.24595631 | Contact: ezzeldinashraf.web@gmail.com", fontsize=7.5, fontname="helv", color=NAVY)

    pdf_out = REPO_ROOT / "COMMERCIAL_DEMO_DECK.pdf"
    doc.save(str(pdf_out))
    doc.close()
    print(f"Generated clean A4 PDF: {pdf_out}")

def main():
    # 1. Write Markdown version
    md_out = REPO_ROOT / "COMMERCIAL_DEMO_DECK.md"
    with open(md_out, "w", encoding="utf-8") as f:
        f.write(MD_CONTENT.strip() + "\n")
    print(f"Generated Markdown deck: {md_out}")

    # 2. Generate PDF version
    generate_pdf()

if __name__ == "__main__":
    main()
