# Product Specification: Erdős Mathematical Verification Engine (EMVE)

**Version:** 1.0.0 (Production Core)  
**Author & Copyright:** Ezzeldin Ashraf Mohamed Shafey Wahba  
**Classification:** Exact Algebraic Computation & Interactive Theorem Proving (Lean 4)  
**Contact:** `ezzeldinashraf.web@gmail.com`  

---

## 1. Executive Summary

The **Erdős Mathematical Verification Engine (EMVE)** is a high-assurance software suite designed to perform **exact, certificate-driven mathematical verification** of discrete dynamical systems, fractal intersections, and arithmetic carry automata. 

Unlike standard numerical tools that suffer from floating-point instability, EMVE pairs **interactive formal verification in Lean 4** with **arbitrary-precision integer linear programming** and **exact algebraic number field root counting** ($\mathbb{Q}(\sqrt{d})$) to deliver mathematically unassailable certificates of boundedness, spectral radii, and invariant measures.

---

## 2. Core Capabilities & Architectural Components

| Component | Technology | Primary Function & Guarantee |
| :--- | :--- | :--- |
| **C1: Interactive Formal Kernel** | **Lean 4 (Mathlib 4.12.0)** | Machine-checked foundational proofs with zero `sorry`. Kernel-verified transfer-matrix dualities ($P M P = M^T$), orbit reachability, and boundary-case spectral bounds under Lean's trusted kernel. |
| **C2: Exact Algebraic Spectral Engine** | **Python 3 / SymPy** | Dual certification of transition spectra: (1) Arbitrary-precision integer Collatz-Wielandt certificates ($5 A v \le 8 v \in \mathbb{Z}$); (2) Exact Sturm sequences in quadratic number fields $\mathbb{Q}(\sqrt{5})$ to count real roots strictly greater than $\phi$. |
| **C3: High-Throughput Rust Scanners** | **Rust (Edition 2021)** | Parallelized, cache-optimized binary automata and middle-state exploration engines (`verify_erdos_rs`, `verify_middle`) executing billions of digit evaluations per second. |
| **C4: Exact Certificate Artifacts** | **Structured CSV / JSON** | Machine-verifiable reference certificates and explicit eigenvector witnesses documenting exact Perron roots, minimal polynomials, and reachability state spaces. |

---

## 3. Commercial Licensing Matrix

| Feature / Permission | Tier 1: Research & Internal | Tier 2: Integration & Development | Tier 3: Production & Deployment |
| :--- | :---: | :---: | :---: |
| **Target Customer** | Quantitative research groups, academic labs | Core technology & formal verification teams | Enterprise automated reasoning & production deployments |
| **Permitted Execution** | Internal computational workflows & reports | Internal systems & development pipelines | Full-scale commercial deployment |
| **Modification Rights** | Operational adaptation (runner/harness only) | Full modification within agreed scope | Full modification & custom pipeline extension |
| **Embedding & Sublicensing** | Internal only (no embedding) | Embeddable in internal proprietary systems | Deployable to production end-users & clients |
| **Generated Output Ownership** | Full ownership of customer-generated outputs | Full ownership of customer-generated outputs | Full ownership of customer-generated outputs |
| **Redistribution of Shipped Source** | Prohibited | Prohibited | Available via custom Schedule A addendum |

---

## 4. Technical Specifications & Performance

- **Supported Platforms:** Linux (Ubuntu 22.04+, Debian 12+, Arch), macOS (Sonoma+ Apple Silicon & Intel).
- **Prerequisites:** Python $\ge 3.10$ (`numpy==2.5.3`, `sympy==1.14.0`), Lean 4 (`v4.12.0`), Rust (`stable`).
- **Scan Throughput:**
  - Python Exact Spectral Scanner: Certified 1,333 multipliers ($M \le 2000$) in **29.1 seconds** (single thread).
  - Rust Middle-State Engine: Over **$10^8$ states/sec** across 16 cores.
- **Verification Guarantee:** Every accepted result is accompanied by an exact algebraic witness (integer vector or sign sequence); floating-point numbers are used solely as candidate heuristics and never determine acceptance.
