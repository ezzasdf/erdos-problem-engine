# Product Specification: Erdős Mathematical Verification Engine (EMVE)

**Version:** 0.9.0 (Technical Preview)  
**Author & Copyright:** Ezzeldin Ashraf Mohamed Shafey Wahba  
**Classification:** Exact Algebraic Computation & Interactive Theorem Proving (Lean 4)  
**Contact:** `ezzeldinashraf.web@gmail.com`  

---

## 1. Executive Summary

The **Erdős Mathematical Verification Engine (EMVE)** is a mathematical verification suite designed to generate **exact, machine-checkable certificates** for discrete dynamical systems, fractal multiplier intersections, and arithmetic carry automata.

Standard numerical packages rely on floating-point linear algebra, which is susceptible to rounding errors and ill-conditioned eigenvalue problems. EMVE addresses this by combining **interactive formal verification in Lean 4** with **arbitrary-precision integer linear programming** and **exact algebraic root counting in $\mathbb{Q}(\sqrt{5})$**. This architecture delivers exact certificates that can be independently audited and checked under stated mathematical assumptions.

> **Foundational Principle:** Exact arithmetic certifies the algebraic and spectral properties of the explicitly constructed transition graphs and matrices under stated definitions. It does not, by itself, replace surrounding analytical proofs (such as the real-line Frostman measure bridge) or prove unverified global graph reachability properties.

---

## 2. Core Capabilities & Architectural Components

| Component | Technology | Primary Function & Exact Guarantees |
| :--- | :--- | :--- |
| **C1: Interactive Formal Kernel** | **Lean 4 (Mathlib 4.12.0)** | Foundational, machine-checked proofs with zero `sorry`. Kernel-verified transfer-matrix dualities ($P M P = M^T$), orbit reachability, Parry measure cylinder weight positivity on the primitive component $\mathcal{C}_*$, and boundary-case bounds. |
| **C2: Exact Algebraic Spectral Engine** | **Python 3 / SymPy** | Dual certification of zero-reachable transition spectra: (1) Arbitrary-precision integer Collatz-Wielandt certificates ($5 A v \le 8 v \in \mathbb{Z}$); (2) Exact Sturm sequences in $\mathbb{Q}(\sqrt{5})$ counting real roots strictly greater than $\phi$ for candidate extremizers. |
| **C3: High-Throughput Exploration Engines** | **Rust (Edition 2021)** | Parallelized binary automata and carry propagation scanners (`verify_erdos_rs`, `verify_middle`) for large-scale combinatorial state space exploration. |
| **C4: Exact Certificate Artifacts** | **Structured CSV / JSON** | Machine-readable verification certificates documenting exact Perron roots, minimal polynomials, integer bounding vectors, and reachable state counts. |

---

## 3. Benchmark Methodology & Measured Performance

All performance metrics are measured under reproducible workloads on standard modern hardware:

- **Benchmark Environment:** AMD Ryzen 9 5950X (16 physical cores, 32 threads, 3.4 GHz base / 4.9 GHz boost), 64 GB DDR4 RAM, Linux (Kernel 6.8).
- **Workload 1 (Python Single-Thread Spectral Certification):**
  - *Task:* Sequential generation of zero-reachable graphs, integer Collatz-Wielandt vector verification, and $\mathbb{Q}(\sqrt{5})$ Sturm sequences for all 1,333 multipliers $2 \le M \le 2000$ with $\gcd(M, 3) = 1$.
  - *Measurement:* End-to-end wall clock time via `time python3 scripts/cantor_multiplier/verify_dimensions.py --scan 2000`.
  - *Result:* **29.1 seconds** total ($\approx 45.8$ certified multipliers per second).
- **Workload 2 (Rust Multi-Threaded State Exploration):**
  - *Task:* Exhaustive carry-chain exploration across window size $k=17$ in `verify_middle` (evaluating $2.8 \times 10^7$ candidate state transitions).
  - *Measurement:* High-resolution monotonic timer across 16 threads (`cargo run --release`).
  - *Result:* **0.32 seconds** execution time ($8.75 \times 10^7$ transitions/second $\approx 87.5$ million transitions/second).
- **Workload 3 (Lean 4 Kernel Check):**
  - *Task:* Full compilation of `BridgeUniform.lean` and dependent modules via `lake build`.
  - *Result:* **2,331 / 2,331 targets built with 0 errors**.

---

## 4. Commercial Licensing Matrix

| Feature / Permission | Tier 1: Research & Internal Use | Tier 2: Integration & Development | Tier 3: Production & Deployment |
| :--- | :---: | :---: | :---: |
| **Primary User** | Academic labs, quantitative research teams | Core algorithm & verification engineers | Enterprise automated reasoning teams |
| **Permitted Scope** | Internal computational runs & research reports | Embedding within proprietary systems | Full production deployment |
| **Modification Rights** | Operational adaptation (runner/harness only) | Full modification within agreed scope | Full modification & custom pipeline extension |
| **Generated Output Rights** | Full ownership of customer-generated outputs | Full ownership of customer-generated outputs | Full ownership of customer-generated outputs |
| **Source Redistribution** | Prohibited | Prohibited | Custom Schedule A addendum |

---

## 5. System Requirements & Prerequisites

- **Operating Systems:** Linux (Ubuntu 22.04+, Debian 12+, Arch), macOS (Sonoma+, Apple Silicon or Intel).
- **Software Dependencies:** Python $\ge 3.10$ (`numpy==2.5.3`, `sympy==1.14.0`), Lean 4 (`v4.12.0`), Rust (`stable`).
- **Independent Verification:** Any recipient can independently run `python3 scripts/test_reproducibility.py` or the standalone auditor `python3 scripts/check_certificate.py` to confirm that all certificates validate in < 0.2 seconds without external network access.
