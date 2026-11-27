# EMVE Certified Multiplier Catalog (`emve-cert-v1`)

This directory contains the pre-computed, independently audited mathematical certificates for all multipliers $2 \le M \le 35$ with $\gcd(M, 3) = 1$ from the Erdős 1939 arithmetic Cantor set intersection problem (Zenodo DOI: [10.5281/zenodo.24595631](https://doi.org/10.5281/zenodo.24595631)).

---

## 1. Summary of Catalog Contents

- **Total Multipliers Certified:** 23
- **Schema Format:** `emve-cert-v1`
- **Integrity Standard:** Canonical SHA-256 payload digest per certificate
- **Independent Audit Status:** 23/23 PASSED (Level 1: Algebraic witness verification; Level 2: Generator derivation consistency)

### Classification Breakdown

1. **Non-Extremizers ($\rho(A) \le 1.60 < \varphi$ strictly):** 19 certificates
   - Certified via pure integer Collatz–Wielandt inequality: $5 \cdot (A v)_i \le 8 \cdot v_i$ with $v \in \mathbb{Z}_{>0}^n$.
   - Multipliers: $M \in \{2, 5, 8, 11, 13, 14, 16, 17, 19, 20, 22, 23, 25, 26, 29, 31, 32, 34, 35\}$.
2. **Proven Extremizers ($\rho(A) = \varphi$ exactly):** 4 certificates
   - Certified via exact polynomial division $(x^2 - x - 1) \mid P(x)$ and Sturm root-counting in $\mathbb{Q}(\sqrt{5})$ showing 0 roots strictly greater than $\varphi$.
   - Multipliers: $M \in \{4, 7, 10, 28\}$.

---

## 2. Catalog Index Table

| Multiplier $M$ | Certificate Type | Matrix Dims | Stated Family | Conclusion | SHA-256 Digest |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **M = 2** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `601955c8...` |
| **M = 4** | `sturm_root_count` | $2 \times 2$ | F1 | $\rho(A) = \varphi$ exactly | `2db5acf9...` |
| **M = 5** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `6cf1e061...` |
| **M = 7** | `sturm_root_count` | $4 \times 4$ | F2 | $\rho(A) = \varphi$ exactly | `2a35fea0...` |
| **M = 8** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `13fddb42...` |
| **M = 10** | `sturm_root_count` | $2 \times 2$ | F1 | $\rho(A) = \varphi$ exactly | `aea23357...` |
| **M = 11** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `79d54101...` |
| **M = 13** | `collatz_wielandt` | $3 \times 3$ | OTHER | $\rho(A) \le 1.60 < \varphi$ | `a66d1d8d...` |
| **M = 14** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `17c05454...` |
| **M = 16** | `collatz_wielandt` | $5 \times 5$ | OTHER | $\rho(A) \le 1.60 < \varphi$ | `929d9f39...` |
| **M = 17** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `9e4d3296...` |
| **M = 19** | `collatz_wielandt` | $6 \times 6$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `148a5dd8...` |
| **M = 20** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `8053edde...` |
| **M = 22** | `collatz_wielandt` | $7 \times 7$ | OTHER | $\rho(A) \le 1.60 < \varphi$ | `9ceb678a...` |
| **M = 23** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `b2a9547f...` |
| **M = 25** | `collatz_wielandt` | $8 \times 8$ | OTHER | $\rho(A) \le 1.60 < \varphi$ | `6339252d...` |
| **M = 26** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `22fb425c...` |
| **M = 28** | `sturm_root_count` | $2 \times 2$ | F1 | $\rho(A) = \varphi$ exactly | `a07d76c1...` |
| **M = 29** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `ebd092bc...` |
| **M = 31** | `collatz_wielandt` | $10 \times 10$ | OTHER | $\rho(A) \le 1.60 < \varphi$ | `2082d37b...` |
| **M = 32** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `dd9ec690...` |
| **M = 34** | `collatz_wielandt` | $8 \times 8$ | OTHER | $\rho(A) \le 1.60 < \varphi$ | `9c1552b2...` |
| **M = 35** | `collatz_wielandt` | $1 \times 1$ | F2 | $\rho(A) \le 1.60 < \varphi$ | `99809dc5...` |

See `catalog_index.json` for machine-readable index metadata.

---

## 3. How to Audit Any Certificate

Run the standalone independent auditor on any file:

```bash
# Audit a single certificate (Level 1: Algebraic witness + SHA-256 integrity)
python3 scripts/check_certificate.py certificates/catalog/M19_collatz_wielandt.json

# Audit with Level 2 generator derivation check
python3 scripts/check_certificate.py --check-derivation certificates/catalog/M19_collatz_wielandt.json

# Audit the entire catalog at once
for f in certificates/catalog/*.json; do
  python3 scripts/check_certificate.py --check-derivation "$f" || exit 1
done
```

---

## 4. Trust Boundaries & Epistemic Scope

1. **Finite Empirical Scope (Not a Universal Theorem)**:
   This catalog establishes the exact spectral radius property ($\rho(A) \le 1.60 < \varphi$ or $\rho(A) = \varphi$) **strictly for the explicit finite set of 23 multipliers listed** ($2 \le M \le 35, \gcd(M, 3) = 1$). It does not claim an exhaustive mathematical proof for all infinitely many multipliers $M$. The universal theorem target remains conditional on hypothesis (H) and the analytical Frostman measure bridge.

2. **Level 2 Consistency vs. Independent Modeling**:
   The Level 2 derivation check (`--check-derivation`) confirms exact consistency between the certificate matrix and metadata against the project's canonical state-space generator (`get_graph_for_M`). It proves that the matrix was not fabricated ad hoc; it does **not** independently re-prove that the graph generator itself correctly models the original arithmetic intersection on the real line (which is a Level 3 analytical obligation).

3. **Decoupled Verification Guarantee**:
   The primary guarantee provided by these certificates is **Level 1 Zero-Trust Algebraic Verification**: given the explicit matrix $A$, the mathematical property ($\rho(A) \le 8/5$ via Collatz–Wielandt or $\rho(A) = \varphi$ via Sturm root-counting) is independently verified with zero floating-point error, independently of how the matrix was discovered.

