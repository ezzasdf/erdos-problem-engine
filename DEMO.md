# Reproducible Commercial Demonstration (5 Minutes)

**Product:** Erdős Mathematical Verification Engine  
**Capability:** Exact Algebraic & Spectral Dimension Certification  
**Target Execution Time:** < 5 seconds  

---

## 1. The Mathematical Context

For integer multipliers $M \ge 1$, we consider the arithmetic intersection of the middle-thirds Cantor set with its dilate:
$$C(1, M) = \Sigma \cap M^{-1} \Sigma, \qquad \Sigma = \left\{ \sum_{j=1}^\infty \frac{d_j}{3^j} : d_j \in \{0, 2\} \right\}.$$

In foundational work on arithmetic intersections of $3$-adic Cantor sets, Abram, Bolshakov, and Lagarias (2015) proved that the particular family of intersections with multipliers $M = 3^k + 1$ attains Hausdorff dimension $\log_3 \phi \approx 0.438018$ (where $\phi = (1+\sqrt{5})/2$), and established that $\log_3 \phi$ bounds the Hausdorff dimension of the exceptional set of non-empty translates.

Our research investigates the broader question across the entire digitwise-safe class of multipliers: whether $\dim_H C(1, M) \le \log_3 \phi$ holds universally across all safe multipliers, and which multipliers attain this extremal value.

**The Computational Verification Goal:**  
Given a safe multiplier $M$, construct the canonical zero-reachable transition matrix $A$, rigorously certify whether its spectral radius satisfies $\lambda_0(M) \le \phi$, identify whether it attains the golden value $\phi$ exactly, and produce machine-checkable certificates **without floating-point rounding errors**.

---

## 2. The Verification Tool

The verification engine provides:
- **`scripts/cantor_multiplier/verify_dimensions.py`**: A dual-engine exact certificate validator.
- **Engine 1: Collatz-Wielandt Linear Integer Certificate**:
  Finds a positive integer vector $v \in \mathbb{Z}_{>0}^n$ such that:
  $$5 \cdot (A v) \le 8 \cdot v \implies \rho(A) \le \frac{8}{5} = 1.60 < \phi \approx 1.618034.$$
  Evaluated using pure Python arbitrary-precision integers (immune to integer overflow and floating-point errors).
- **Engine 2: Exact Sturm Sequence in $\mathbb{Q}(\sqrt{5})$**:
  Computes the exact characteristic polynomial $P(x) = \det(x I - A) \in \mathbb{Z}[x]$, performs polynomial division by the golden polynomial $x^2 - x - 1$, and evaluates the exact sign chain of the Sturm sequence in the quadratic number field $\mathbb{Q}(\sqrt{5})$ to count the exact number of real roots strictly greater than $\phi$.

---

## 3. Execution Commands

From the repository root, run the two standard verification tasks:

### Test A: Fast Certified Scan ($2 \le M \le 10$)
```bash
python3 scripts/cantor_multiplier/verify_dimensions.py --scan 10
```

### Test B: Representative Dimension Table
```bash
python3 scripts/cantor_multiplier/verify_dimensions.py
```

### Test C: Automated Customer-Independent Regression Test
```bash
python3 scripts/test_reproducibility.py
```

### Test D: Standalone Independent Certificate Auditor (Raw Witnesses)
```bash
python3 scripts/check_certificate.py --example
```

### Test E: Portable Certificate Verification (Zero-Trust JSON Check)
```bash
python3 scripts/check_certificate.py certificates/M19_collatz_wielandt.json certificates/M7_sturm_extremizer.json
```

---

## 4. Expected Results & Output Report

### Test A Output:
```text
Starting Algebraic Scan 2 <= M <= 10, gcd(M,3) = 1 (mode: exact)...

Exact Algebraic Scan Summary (2 <= M <= 10, gcd(M,3) = 1):
  Exact CW integer certificates (lambda <= 1.60) : 3
  Exact Sturm sequence certificates (in Q(sqrt5)): 3
  Multipliers with lambda(M) > phi               : none
  Multipliers attaining lambda(M) = phi          : [4, 7, 10]
  Extremizers predicted by Theorem 1             : [4, 7, 10]
  Overall Verification Status                     : PASSED (ALL MULTIPLIER GRAPHS IN SCAN M <= 10 EXACTLY CERTIFIED lambda_0 <= phi)
```

### Test B Output:
```text
log_3(phi) = 0.438017879

    M  states       lambda   inferred_dim  status                   perron factor        certificate
-----------------------------------------------------------------------------------------------------------------------
    1       1  2.000000000       0.630930  EXCEEDS_PHI              x - 2                Sturm sequence: 1 real root(s) > phi
    2       1  1.000000000       0.000000  EXACT_STRICTLY_LESS_PHI  -                    Collatz-Wielandt integer vector 5*A*v <= 8*v (rho <= 1.60 < phi)
    3       2  2.000000000       0.630930  EXCEEDS_PHI              x - 2                Sturm sequence: 1 real root(s) > phi
    4       2  1.618033989       0.438018  EXACT_EQUAL_PHI          x**2 - x - 1         Exact match (x^2 - x - 1) | P(x) with 0 roots > phi; lambda = phi
    7       4  1.618033989       0.438018  EXACT_EQUAL_PHI          x**2 - x - 1         Exact match (x^2 - x - 1) | P(x) with 0 roots > phi; lambda = phi
   10       2  1.618033989       0.438018  EXACT_EQUAL_PHI          x**2 - x - 1         Exact match (x^2 - x - 1) | P(x) with 0 roots > phi; lambda = phi
   19       6  1.465571232       0.347934  EXACT_STRICTLY_LESS_PHI  -                    Collatz-Wielandt integer vector 5*A*v <= 8*v (rho <= 1.60 < phi)
   25       8  1.465571232       0.347934  EXACT_STRICTLY_LESS_PHI  -                    Collatz-Wielandt integer vector 5*A*v <= 8*v (rho <= 1.60 < phi)
   28       2  1.618033989       0.438018  EXACT_EQUAL_PHI          x**2 - x - 1         Exact match (x^2 - x - 1) | P(x) with 0 roots > phi; lambda = phi
   55       8  1.380277569       0.293356  EXACT_STRICTLY_LESS_PHI  -                    Collatz-Wielandt integer vector 5*A*v <= 8*v (rho <= 1.60 < phi)
   61      14  1.570147312       0.410672  EXACT_STRICTLY_LESS_PHI  -                    Collatz-Wielandt integer vector 5*A*v <= 8*v (rho <= 1.60 < phi)
   73      16  1.618033989       0.438018  EXACT_EQUAL_PHI          x**2 - x - 1         Exact match (x^2 - x - 1) | P(x) with 0 roots > phi; lambda = phi
   79      16  1.380277569       0.293356  EXACT_STRICTLY_LESS_PHI  -                    Collatz-Wielandt integer vector 5*A*v <= 8*v (rho <= 1.60 < phi)
   82       2  1.618033989       0.438018  EXACT_EQUAL_PHI          x**2 - x - 1         Exact match (x^2 - x - 1) | P(x) with 0 roots > phi; lambda = phi
  163      10  1.324717957       0.255959  EXACT_STRICTLY_LESS_PHI  -                    Collatz-Wielandt integer vector 5*A*v <= 8*v (rho <= 1.60 < phi)
  217      22  1.409235235       0.312255  EXACT_STRICTLY_LESS_PHI  -                    Collatz-Wielandt integer vector 5*A*v <= 8*v (rho <= 1.60 < phi)
  235      30  1.409235235       0.312255  EXACT_STRICTLY_LESS_PHI  -                    Collatz-Wielandt integer vector 5*A*v <= 8*v (rho <= 1.60 < phi)
  244       2  1.618033989       0.438018  EXACT_EQUAL_PHI          x**2 - x - 1         Exact match (x^2 - x - 1) | P(x) with 0 roots > phi; lambda = phi

Note: 'inferred_dim' is log_3(lambda_0), the symbolic growth rate of the zero-reachable forward SFT graph.
      It equals the true Hausdorff dimension dim_H on R when the reachability correspondence and
      analytical Frostman bridge hold (proven for extremizers and boundary rays; conditional on Hypothesis (H) in interior).
```

### Test E Output (Portable Certificate Audit):
```text
================================================================================
EMVE Independent Certificate Auditor: Auditing Portable Certificates
Checker: EMVE Independent Certificate Auditor v0.9.0
================================================================================

Target File    : certificates/M19_collatz_wielandt.json
Problem ID     : erdos-cantor-multiplier:M=19:family=2:lag=(1,3)
Format Version : emve-cert-v1
Cert Type      : collatz_wielandt
SHA-256 Digest : 49fdbcaac0f47ba27a9653147d1d5df64d4efff5f9f59d69d44dcc454892bfbc
Audit Status   : [PASS]
Proof Details  : Collatz-Wielandt verified: 5*(A@v) <= 8*v holds across all 6 rows. Proves rho(A) <= 8/5 = 1.60 < phi strictly.
Execution Time : 0.0001s

Target File    : certificates/M7_sturm_extremizer.json
Problem ID     : erdos-cantor-multiplier:M=7:family=2:lag=(1,2)
Format Version : emve-cert-v1
Cert Type      : sturm_root_count
SHA-256 Digest : 970de11745cd4f47fe42113f8072e918a72076c1fcc30cad2f6ae080cf9d569e
Audit Status   : [PASS]
Proof Details  : Sturm sequence verified: (x^2 - x - 1) | P(x) with 0 real roots > phi. Proves rho(A) = phi exactly.
Execution Time : 0.0689s

================================================================================
AUDIT SUMMARY: ALL 2 CERTIFICATES INDEPENDENTLY AUDITED AND PASSED.
Guarantees: Valid SHA-256 payload digest; exact mathematical inequality satisfied in Z or Q(sqrt5).
================================================================================
```

---

## 5. Trust Boundary: What Was Verified vs. What Was Not

| Property | Status | Verification Guarantee |
| :--- | :---: | :--- |
| **Exact Spectral Radius $\lambda_0(M) = \phi$** | **VERIFIED** | Proved for $M \in \{4, 7, 10, 28, 73, 82, 244\}$ via exact polynomial factorisation $(x^2 - x - 1) \mid P(x)$ and Sturm sign evaluations in $\mathbb{Q}(\sqrt{5})$. |
| **Strict Upper Bound $\lambda_0(M) \le 1.60 < \phi$** | **VERIFIED** | Proved for tested non-extremizers via pure integer Collatz-Wielandt vectors $5 A v \le 8 v \in \mathbb{Z}$. |
| **Zero-Reachable State Space** | **VERIFIED** | Constructed by exact breadth-first graph traversal from the canonical zero state $0^b$. |
| **Infinite Universal Bound ($M \to \infty$)** | **CONDITIONAL** | Analytical proof for the interior domain relies on Hypothesis~(H) (Parry cylinder weight slack inequality). |
| **Full $2^b$ SFT Graph Decomposition** | **UNVERIFIED** | The script analyzes the zero-reachable forward component $\mathcal{G}_0$, not the full $2^b$ state space. |
| **Measure-Theoretic Dimension Bridge** | **ANALYTICAL** | The Frostman measure bridge connecting word counts to Hausdorff measure on $\mathbb{R}$ is an analytical paper proof (§3), not an automated code check. |
