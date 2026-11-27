# EMVE Benchmark Evidence & Reproducibility Record

**Release Target:** `emve-cert-v1.0.0`  
**Git Commit:** `387906cb8798e3b1c97a78370e704db424f6050b` (and subsequent release commits)  
**Zenodo DOI:** [10.5281/zenodo.24595631](https://doi.org/10.5281/zenodo.24595631)  
**Date of Calibration:** November 27, 2026  

---

## 1. Test Environment Specifications

| Component | Specification |
| :--- | :--- |
| **CPU** | AMD Ryzen 9 5950X (16 physical cores, 32 hardware threads, 3.4 GHz base / 4.9 GHz boost) |
| **Memory** | 64 GB DDR4-3200 (Dual-channel) |
| **Operating System** | Linux (Ubuntu 24.04 LTS / Pop!_OS, kernel 6.8 / 7.2 x86_64) |
| **Python Toolchain** | Python 3.12.3 (CPython), SymPy 1.14.0, NumPy 2.5.3 |
| **Rust Toolchain** | `rustc` 1.82.0 (stable), `cargo` 1.82.0 (Edition 2021, release profile with `opt-level = 3`) |
| **Lean Toolchain** | Lean 4.12.0 (commit `809c3fb3b5c8`, zero external dependencies for `CertCheck.lean`) |

---

## 2. Benchmark Suites & Exact Methodology

### Benchmark 1: Standalone Integer Certificate Auditor (M = 19)
- **Target:** Multiplier $M = 19$ ($6 \times 6$ matrix, Collatz–Wielandt witness vector $v \in \mathbb{Z}^6$).
- **Measurement Distinction:**
  - **In-Process Algorithmic Audit (`verify_portable_certificate_dict`):**  
    Measures pure mathematical validation (SHA-256 canonical hashing + Collatz–Wielandt matrix inequality + strict integer type enforcement) without Python interpreter initialization overhead.
    - *Methodology:* Evaluated over 1,000 iterations via Python `timeit`:
      ```bash
      python3 -c "
      import timeit, json, sys
      sys.path.insert(0, 'scripts')
      from check_certificate import verify_portable_certificate_dict
      cert = json.load(open('eval_package/M19_collatz_wielandt.json'))
      t = timeit.timeit(lambda: verify_portable_certificate_dict(cert), number=1000)
      print(f'Mean in-process verification time: {t/1000:.6f} s ({t:.3f} ms / 1k runs)')
      "
      ```
    - *Observed Result:* **0.000086 seconds (86 microseconds)** per certificate.
  - **End-to-End CLI Invocation:**  
    Measures the full command-line execution including CPython 3.12 process startup, standard library module imports (`json`, `hashlib`, `fractions`, `argparse`), and console reporting.
    - *Copy-Pastable Command:*
      ```bash
      time python3 scripts/check_certificate.py eval_package/M19_collatz_wielandt.json
      ```
    - *Observed Result:* **~0.10 seconds** wall-clock time.

---

### Benchmark 2: Clean-Room Evaluation & Full 23-Multiplier Catalog Audit
- **Target:** Complete archive unpack into `/tmp` and audit of all 23 catalog certificates ($2 \le M \le 35, \gcd(M, 3) = 1$) plus 4 negative corruption tests.
- **Copy-Pastable Command:**
  ```bash
  python3 scripts/test_clean_environment.py
  ```
- **Observed Result:** 
  - Extracted 5 files/directories from `eval_package.zip` in an isolated temporary directory.
  - Audited all 23 extracted catalog certificates: **23/23 PASSED** (0.001s–0.004s per certificate).
  - Evaluated 4 corruption and tampering attacks: all 4 rejected with clean `[FAIL]` and zero uncaught exceptions.
  - Total elapsed script time: **0.11 seconds**.

---

### Benchmark 3: Python Sequential Algebraic Scan ($2 \le M \le 2000$)
- **Target:** Sequential graph generation, integer Collatz–Wielandt vector generation, and Sturm root counting across 1,333 candidate moduli ($2 \le M \le 2000$ with $\gcd(M, 3) = 1$).
- **Copy-Pastable Command:**
  ```bash
  python3 scripts/cantor_multiplier/verify_dimensions.py --scan 2000
  ```
- **Benchmark Methodology:**
  Single-run wall-clock timing on a single thread of the AMD Ryzen 9 5950X:
  ```bash
  time python3 scripts/cantor_multiplier/verify_dimensions.py --scan 2000
  ```
- **Observed Output & Timings:**
  - Total Moduli Evaluated: 1,333
  - Exact Collatz–Wielandt certificates ($\rho(A) \le 1.60 < \varphi$): 1,318
  - Exact Sturm sequence certificates ($\rho(A) = \varphi$ in $\mathbb{Q}(\sqrt{5})$): 15
  - Moduli with $\rho(A) > \varphi$: 0 (none)
  - Wall Clock Time: **29.12 seconds** ($\approx 45.8$ certified moduli per second).

---

### Benchmark 4: Rust Multi-Threaded State Exploration Engine (`verify_erdos_rs`)
- **Target:** Parallelized two-sided search engine (`verify_erdos_rs`) exploring candidate carry branches across window size $K = 17, k' = 17$ using Rayon across all CPU cores.
- **Copy-Pastable Command:**
  ```bash
  cd verify_erdos_rs && cargo run --release -- --two-sided 17 17
  ```
- **Benchmark Methodology:**
  Compiled with Cargo release profile (`opt-level = 3`). Evaluated using high-resolution monotonic timer (`std::time::Instant`).
- **Observed Result:**
  - Parallel Depth: 14 (8,192 parallel branches).
  - Evaluated Branches: 8,192 / 8,192.
  - Elapsed Time: **34.67 milliseconds (0.035 seconds)**.
  - Candidates Found: 3 ($n \in \{0, 2, 8\}$).
  - Throughput: $\approx 2.36 \times 10^5$ branches per second.

---

### Benchmark 5: Lean 4 Standalone Kernel Verification (`CertCheck.lean`)
- **Target:** Standalone Lean 4 file verifying $M=19$ Collatz–Wielandt certificate plus 6 negative regression theorems covering 5 failure categories.
- **Copy-Pastable Command:**
  ```bash
  lean lean/CertCheck.lean
  ```
- **Observed Result:**
  - Kernel reduction (`by rfl`): 0.04 seconds compilation & evaluation time.
  - Axioms introduced: **Zero (`[]`)**.
