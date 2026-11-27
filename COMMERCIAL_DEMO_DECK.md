# Decoupled High-Assurance Verification for Discrete Dynamical Systems
## Erdős Mathematical Verification Engine (EMVE) — Executive Technical Brief

**Author:** Ezzeldin Ashraf Mohamed Shafey Wahba (`ezzeldinashraf.web@gmail.com`)  
**Zenodo DOI:** [10.5281/zenodo.24595631](https://doi.org/10.5281/zenodo.24595631) | **GitHub:** [github.com/ezzasdf/erdos-problem-engine](https://github.com/ezzasdf/erdos-problem-engine)  
**Release Version:** `emve-cert-v1.0.0` | **Status:** Technical Preview / Evaluation Kit  

---

### 1. The Challenge: Numerical Uncertainty in Discrete Transition Spectra
Verification pipelines for discrete dynamical systems, carry automata, and state-transition graphs frequently evaluate spectral radius bounds $\rho(A) \le \lambda^*$ to guarantee contractivity, safety invariants, or dimension bounds. Standard numerical packages rely on floating-point eigensolvers (e.g., LAPACK/BLAS). In borderline or ill-conditioned cases, floating-point methods can introduce numerical uncertainty and precision loss. EMVE offers an exact integer-based verification path for supported certificate forms, eliminating floating-point rounding error from the witness audit.

---

### 2. The Solution: Decoupled Proof-Carrying Certificate Architecture
EMVE decouples complex, heuristic state-space exploration from formal witness verification:
- **Heuristic / Combinatorial Exploration (Untrusted):** High-throughput search engines in Rust and Python discover extremal transition graphs and candidate Perron eigenvectors.
- **Integer Collatz–Wielandt Witnesses (Level 1 Verification):** To certify $\rho(A) \le 1.60 < \varphi$, EMVE generates an integer witness vector $v \in \mathbb{Z}_{>0}^n$ and positive scaling integers $c, d$ satisfying $c \cdot (A v) \le d \cdot v$ across all rows. Evaluated purely in arbitrary-precision integer arithmetic (zero floating-point operations).
- **Exact Sturm Root Counting:** For extremal equality ($\rho(A) = \varphi$), EMVE computes the characteristic polynomial, verifies $(x^2 - x - 1) \mid P(x)$, and constructs an exact Sturm chain in $\mathbb{Q}(\sqrt{5})$ to certify 0 real roots exceed $\varphi$.

---

### 3. Three-Level Verification Hierarchy & Trust Boundaries
To eliminate ambiguity, EMVE enforces explicit epistemic boundaries across three verification levels:
1. **Level 1 (Verified Certificate):** Standalone mathematical validation of the explicit matrix $A$. The supplied witness is checked in ~0.0001s in-process via pure Python standard library or inside Lean 4's trusted kernel by definitional reflexivity (`by rfl`) with zero axioms (`[]`).
2. **Level 2 (Verified Derivation):** Confirms reproducibility from the project's canonical state-space generator (`get_graph_for_M`), verifying that matrix dimensions, family parameters, and lags match canonical derivation.
3. **Level 3 (Analytical Theorem):** The continuous Frostman measure bridge connecting symbolic growth rates $\log_3 \lambda_0$ to Hausdorff dimension on $\mathbb{R}$ remains an analytical paper proof conditional on Hypothesis (H).

---

### 4. Measured Performance Benchmarks & Copy-Pastable Commands
Benchmarks evaluated on reference hardware (AMD Ryzen 9 5950X, 16C/32T, 64 GB RAM, Linux 6.8). Full logs in [`benchmarks/BENCHMARK_EVIDENCE.md`](benchmarks/BENCHMARK_EVIDENCE.md):
- **Standalone Auditor:** `python3 scripts/check_certificate.py eval_package/M19_collatz_wielandt.json`  
  *Result:* In-process mathematical audit runs in **~0.0001s (86 µs)** (mean over 1,000 iterations); end-to-end CLI execution is **~0.10s** (including Python 3.12 startup, zero external dependencies).
- **23-Modulus Verified Catalog:** `python3 scripts/check_certificate.py certificates/catalog/M*.json`  
  *Result:* All 23 moduli ($2 \le M \le 35, \gcd(M, 3) = 1$) audited with 100% pass rate (19 Collatz–Wielandt + 4 Sturm).
- **Standalone Lean 4 Module:** `lean lean/CertCheck.lean`  
  *Result:* Compact module (~130 lines) verified in core Lean 4 without Mathlib; includes **six negative regression theorems covering five failure categories** (ragged rows, dimension mismatches, non-positive witness entries, zero multipliers $c$ and $d$, and false inequalities).
- **Rust Exploration Engine:** `cd verify_erdos_rs && cargo run --release -- --two-sided 17 17`  
  *Result:* Multi-threaded Rayon engine evaluates 8,192 candidate branches across 16 threads in **34.7 milliseconds (0.035s)**.
- **Python Sequential Scan:** `python3 scripts/cantor_multiplier/verify_dimensions.py --scan 2000`  
  *Result:* Single-run certification of 1,333 moduli ($2 \le M \le 2000$) in **29.1s** ($\approx 45.8$ certified moduli/sec).

---

### 5. Target Domains for Evaluation & Collaborative Pilot Roadmap
- **Target Applications for Evaluation:**
  - *Cryptographic Carry Circuits & SMT Pipelines:* Target domain for proving absence of carry-chain overflow without floating-point relaxation.
  - *Discrete Control Automata & State Machines:* Target domain for bounding transition matrix growth rates with deductive certainty.
  - *Interactive Theorem Prover Tactics:* Target domain for direct ingestion of integer witness vectors into Lean 4, Coq, and Isabelle/HOL.
- **Collaborative Pilot Framework:**
  - Structured 4-week technical evaluation to assess solver scalability, generate domain-specific witness certificates, and validate integration feasibility into client audit toolchains.
