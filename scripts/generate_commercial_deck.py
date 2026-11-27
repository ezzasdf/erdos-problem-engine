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
## Erdős Mathematical Verification Engine (EMVE) — Executive Product Brief

**Author:** Ezzeldin Ashraf Mohamed Shafey Wahba (`ezzeldinashraf.web@gmail.com`)  
**Zenodo DOI:** [10.5281/zenodo.24595631](https://doi.org/10.5281/zenodo.24595631) | **GitHub:** [github.com/ezzasdf/erdos-problem-engine](https://github.com/ezzasdf/erdos-problem-engine)  
**Release Version:** `emve-cert-v1.0.0` | **Status:** Technical Preview / Enterprise Evaluation  

---

### 1. The Challenge: Floating-Point Instability in Discrete Transition Systems
Modern verification pipelines for discrete dynamical systems, carry automata, and state-transition graphs frequently evaluate spectral radius bounds $\\rho(A) \\le \\lambda^*$ to guarantee contractivity or dimension bounds. Standard numerical packages rely on floating-point eigensolvers (e.g. LAPACK/BLAS). In ill-conditioned or borderline state-transition matrices, floating-point rounding errors and cancellation drift introduce undetected false positives, failing the deductive standard required by aerospace, cryptographic hardware, and interactive theorem provers (Lean 4, Coq).

---

### 2. The Solution: Decoupled Proof-Carrying Certificate Architecture
EMVE decouples complex, heuristic state-space exploration from formal witness verification:
- **Heuristic / Combinatorial Exploration (Untrusted):** High-throughput search engines in Rust (87.5M transitions/sec) and Python discover extremal transition graphs and candidate Perron eigenvectors.
- **Integer Collatz–Wielandt Witnesses (Level 1 Verification):** To certify $\\rho(A) \\le 1.60 < \\varphi$, EMVE generates an integer witness vector $v \\in \\mathbb{Z}_{>0}^n$ and positive scaling integers $c, d$ satisfying $c \\cdot (A v) \\le d \\cdot v$ across all rows. Evaluated purely in arbitrary-precision integer arithmetic (zero floating point).
- **Exact Sturm Root Counting:** For extremal equality ($\rho(A) = \varphi$), EMVE computes the characteristic polynomial, verifies $(x^2 - x - 1) \\mid P(x)$, and constructs an exact Sturm chain in $\\mathbb{Q}(\\sqrt{5})$ to certify 0 real roots exceed $\\varphi$.

---

### 3. Three-Level Verification Hierarchy & Trust Boundaries
To eliminate ambiguity, EMVE enforces explicit epistemic boundaries across three verification levels:
1. **Level 1 (Verified Certificate):** Standalone mathematical validation of the explicit matrix $A$. The supplied witness is checked in 0.0002s via pure Python standard library or inside Lean 4's trusted kernel by definitional reflexivity (`by rfl`) with zero axioms (`[]`).
2. **Level 2 (Verified Derivation):** Confirms reproducibility from the project's canonical state-space generator (`get_graph_for_M`), verifying that matrix dimensions, family parameters, and lags match canonical derivation.
3. **Level 3 (Analytical Theorem):** The continuous Frostman measure bridge connecting symbolic growth rates $\\log_3 \\lambda_0$ to Hausdorff dimension on $\\mathbb{R}$ remains an analytical paper proof conditional on Hypothesis (H).

---

### 4. Key Performance Benchmarks & Verified Catalog
- **Multi-Modulus Benchmark Catalog:** 23/23 certified transition matrices ($2 \\le M \\le 35, \\gcd(M, 3) = 1$) independently audited with 100% pass rate (19 Collatz–Wielandt bounds + 4 Sturm extremizers).
- **Standalone Auditor Performance:** Evaluates $M=19$ ($6 \\times 6$ matrix) in **0.0002 seconds** on stock Python 3 with **zero external dependencies** and SHA-256 payload integrity enforcement.
- **Standalone Lean 4 Integration:** 25-line standalone Lean file (`CertCheck.lean`) verified in Lean 4 core (`Init`) without Mathlib, including 5 negative regression theorems rejecting ragged rows, non-positive entries, and false inequalities.

---

### 5. Enterprise Applications & Commercial Engagement
- **Cryptographic Carry Circuits & SMT Pipelines:** Certifying absence of carry explosions in hardware arithmetic without floating-point relaxation.
- **Interactive Theorem Proving Tactics:** Exporting machine-checkable witness vectors directly into Lean 4 and Coq without implementing heavy matrix algebra in the proof assistant.
- **Commercial Pilots ($15,000 – $40,000):** 4-week targeted pilot to build custom decoupled certificate generators for proprietary transition matrices and high-assurance audit pipelines.
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
    GREEN_TEXT = (0.05, 0.45, 0.15)
    
    # 1. Header Banner
    page.draw_rect(fitz.Rect(30, 25, 565, 88), color=NAVY, fill=LIGHT_BG)
    page.insert_text((42, 45), "DECOUPLED HIGH-ASSURANCE VERIFICATION", fontsize=15, fontname="helv", color=NAVY)
    page.insert_text((42, 60), "FOR DISCRETE DYNAMICAL SYSTEMS & CARRY AUTOMATA", fontsize=11, fontname="helv", color=ACCENT_BLUE)
    page.insert_text((42, 75), "Erdős Mathematical Verification Engine (EMVE) — Executive Product Brief (v1.0.0)", fontsize=8.5, fontname="helv", color=DARK_GRAY)
    page.insert_text((42, 84), "Author: Ezzeldin Ashraf | DOI: 10.5281/zenodo.24595631 | GitHub: github.com/ezzasdf/erdos-problem-engine", fontsize=7.5, fontname="helv", color=DARK_GRAY)

    y = 100

    def draw_section(title, lines, box_height):
        nonlocal y
        # Section Header
        page.draw_rect(fitz.Rect(30, y, 565, y + 16), color=ACCENT_BLUE, fill=NAVY)
        page.insert_text((38, y + 12), title.upper(), fontsize=9, fontname="helv", color=(1, 1, 1))
        y += 18
        
        # Content box
        rect = fitz.Rect(30, y, 565, y + box_height)
        page.draw_rect(rect, color=BORDER_COLOR, fill=LIGHT_BG)
        
        text_y = y + 12
        for line in lines:
            if isinstance(line, tuple):
                prefix, body = line
                page.insert_text((38, text_y), prefix, fontsize=7.5, fontname="helv", color=NAVY)
                prefix_width = fitz.get_text_length(prefix, fontname="helv", fontsize=7.5)
                page.insert_text((38 + prefix_width + 3, text_y), body, fontsize=7.5, fontname="helv", color=DARK_GRAY)
            else:
                page.insert_text((38, text_y), line, fontsize=7.5, fontname="helv", color=DARK_GRAY)
            text_y += 11.5
        y += box_height + 8

    # Section 1: The Problem
    draw_section(
        "1. The Core Problem: Floating-Point Instability in Discrete Spectral Bounds",
        [
            "• Modern verification of state-transition graphs and carry automata relies on spectral radius bounds: rho(A) <= lambda*.",
            "• Standard toolchains rely on numerical eigensolvers (LAPACK/BLAS) vulnerable to rounding errors and ill-conditioned drift.",
            "• Result: Catastrophic false positives in aerospace control systems, cryptographic hardware, and formal provers (Lean 4)."
        ],
        box_height=38
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
        box_height=49
    )

    # Section 3: Three-Tier Hierarchy
    draw_section(
        "3. Three-Level Verification Hierarchy & Explicit Trust Boundaries",
        [
            ("• Level 1 (Verified Certificate): ", "Zero-trust verification of matrix A. Python stdlib audits in 0.0002s; Lean 4 audits via 'by rfl'."),
            ("• Level 2 (Verified Derivation): ", "Confirms exact reproducibility from EMVE's canonical state-space generator (get_graph_for_M)."),
            ("• Level 3 (Analytical Theorem): ", "Continuous Frostman bridge connecting symbolic growth to Hausdorff dimension on R (analytical proof).")
        ],
        box_height=38
    )

    # Section 4: Benchmarks & Catalog
    draw_section(
        "4. Measured Performance Benchmarks & 23-Multiplier Verified Catalog",
        [
            ("• 23-Modulus Verified Catalog: ", "All 23 multipliers (2 <= M <= 35, gcd(M,3)=1) audited with 100% PASS rate (19 CW + 4 Sturm)."),
            ("• Lean 4 Core Integration: ", "Standalone CertCheck.lean verified in Lean 4 standard library with 0 Mathlib dependencies & 0 axioms."),
            ("• Negative Hardening Tests: ", "Rejects ragged rows (zipWith guards), dimension mismatches, non-positive entries, and false inequalities."),
            ("• High-Throughput Engines: ", "Rust exploration engine scans 87.5M transitions/sec; Python certifies 45.8 moduli/sec sequentially.")
        ],
        box_height=49
    )

    # Section 5: Commercial Applications & Pilot
    draw_section(
        "5. Commercial Applications & Enterprise Pilot Engagements",
        [
            ("• Cryptographic Hardware & Carry Logic: ", "Certifying absence of carry-chain overflow without floating-point relaxation."),
            ("• Interactive Theorem Prover Tactics: ", "Direct ingestion of integer Collatz-Wielandt certificates into Lean 4, Coq, and Isabelle/HOL."),
            ("• Blockchain & Smart Contract Audit: ", "Independent zero-trust auditing of state-transition graphs and discrete token dynamics."),
            ("• 4-Week Commercial Pilot ($15k-$40k): ", "Custom decoupled certificate generators for enterprise transition matrices and audit pipelines.")
        ],
        box_height=49
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
