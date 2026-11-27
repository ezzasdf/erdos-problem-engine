# EMVE Technical Evaluation Package (v1.0.0)

This self-contained package allows you to independently audit an exact mathematical witness for multiplier $M = 19$ in seconds, with **zero external dependencies** for the Collatz–Wielandt path.

---

## 1. Quick Start: One Command

Run the standalone checker from this directory using stock Python 3 (pure standard library; no `pip install` required):

```bash
python3 check_certificate.py M19_collatz_wielandt.json
```

### Expected Output (observed reference time: ~0.0002s on AMD Ryzen 9 5950X):

```text
================================================================================
EMVE Independent Certificate Auditor: Auditing Portable Certificates
Checker: EMVE Independent Certificate Auditor v1.0.0
Derivation Check: DISABLED (decoupled matrix-only check)
================================================================================

Target File        : M19_collatz_wielandt.json
Problem ID         : erdos-cantor-multiplier:M=19:family=2:lag=(1,3)
Format Version     : emve-cert-v1
Cert Type          : collatz_wielandt
Integrity Checksum : a939b267b971c7a51fc448d6a2b4da028d9ec97d5f1aadfe0b64036bf579b1a2
Audit Status       : [PASS]
Proof Details      : Collatz-Wielandt verified: 5*(A@v) <= 8*v holds across all 6 rows. Proves rho(A) <= 8/5 = 1.60 < phi strictly.
Execution Time     : 0.0002s

================================================================================
AUDIT SUMMARY: ALL 1 CERTIFICATES INDEPENDENTLY AUDITED AND PASSED.
Guarantees: Strict integer typing; verified SHA-256 integrity checksum; exact spectral bound.
Notice: Checked matrix properties. Run with --verify-derivation to re-derive matrix from M.
================================================================================
```
*(Note: Execution time is an observed benchmark on the reference environment; actual execution time may vary depending on CPU and Python interpreter initialization).*

---

## 2. Package Contents & Dependency Scope

- **`check_certificate.py`**: Standalone mathematical certificate auditor. The Collatz–Wielandt evaluation implemented here operates with **zero external dependencies** on Python 3 standard library (`json`, `hashlib`, `fractions`, `argparse`). *(Note: The full repository version of this script lazily imports SymPy if auditing quadratic-field Sturm sequences, and NumPy if running `--verify-derivation`; neither is required for this M=19 package).*
- **`M19_collatz_wielandt.json`**: Portable certificate (`emve-cert-v1`) for multiplier $M = 19$. Contains the full $6 \times 6$ integer transition matrix $A$, the positive integer witness vector $v = [201563, 139062, 100000, 100000, 139062, 201562]$, and the SHA-256 integrity checksum.
- **`README.md`**: This guide.

---

## 3. What IS and What IS NOT Proved

To maintain rigorous scientific standards, we explicitly separate what this certificate proves from surrounding analytical context:

### What IS Proved by this Package:
1. **Exact Upper Bound:** The auditor verifies that $5 \sum_j A_{ij} v_j \le 8 v_i$ holds for every row $i \in \{0, \dots, 5\}$ in pure arbitrary-precision integers $\mathbb{Z}$. By the Collatz–Wielandt theorem for nonnegative matrices, this rigorously proves:
   $$\rho(A) \le \frac{8}{5} = 1.60 < \phi \approx 1.618034.$$
2. **Zero Floating-Point Error:** Acceptance is evaluated purely in $\mathbb{Z}$; no floating-point eigenvalue approximation is used.
3. **Payload Integrity:** The mandatory SHA-256 integrity checksum confirms that the JSON witness was not corrupted or truncated in transit.
4. **Strict Typing:** All entries are verified to be strictly integers; booleans (`True`/`False`) are explicitly rejected.

### What IS NOT Proved by this Package:
1. **Automaton Derivation:** The auditor verifies properties of the matrix $A$ encoded in the JSON. It does not independently construct the carry graph from $M = 19$ (end-to-end derivation requires the full repository).
2. **Global Two-Sided Uniqueness:** Proof that the zero-reachable component uniquely dominates the full two-sided shift space across the interior domain relies on an analytical spectral-gap hypothesis (Hypothesis (H)).
3. **Continuous Measure Bridge:** The Frostman measure bridge connecting symbolic growth rates $\log_3 \lambda_0$ to real-line Hausdorff dimension $\dim_H C(1, 19)$ on $\mathbb{R}$ is an analytical paper proof (§3), not an automated script check.
4. **Cryptographic Provenance:** The SHA-256 checksum detects corruption; author authenticity should be checked against the official Zenodo archive record or the canonical Git release tag (note: the Git tag identifies the source commit, but is not GPG-signed).

---

## 4. Contact & Citation

- **Author:** Ezzeldin Ashraf Mohamed Shafey Wahba (`ezzeldinashraf.web@gmail.com`)
- **Zenodo Archive Record:** [DOI: 10.5281/zenodo.24595631](https://zenodo.org/records/24595631)
- **Repository:** https://github.com/ezzasdf/erdos-problem-engine
