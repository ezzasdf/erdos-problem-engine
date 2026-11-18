"""Third family hunt + log-bound push via the family-2 proof framework.

Framework (from x2p_family2_proof.py): if M = P(3^k) with signed block filter
P(y) = sum_q c_q y^q where ALL subset-sums of {c_q} lie in [-1, 2] and c_0 in {0,1},
then columns factorize: dim = log_3(growth of per-column SFT
    y_r + sum_{q>0} c_q y_{r-q} in {0,1},  y_{<0} = 0).

Sections:
  S1  classify ALL safe patterns (bounded degree) -> expect {1+y^a} U {1-y^a+y^b}
  S2  per-(a,b) column growth lambda(a,b); check lambda <= phi, equality iff b=2a
  S3  cross-check dim_numeric(3^b - 3^a + 1) == log_3 lambda
  S4  exact new dims: charpoly of column SFT for each (a,b)
  S5  bound push: M = 3^m * (safe form), dim <= log_3 phi on whole safe class
"""
import math, itertools, importlib.util

spec = importlib.util.spec_from_file_location("dt", "x2p_dim_table.py")
dt = importlib.util.module_from_spec(spec); spec.loader.exec_module(dt)

L3 = math.log(3.0)
PHI = (1 + math.sqrt(5)) / 2
DPHI = math.log(PHI) / L3
F = [0, 1]
for _ in range(2, 500):
    F.append(F[-1] + F[-2])


def subset_sums(coeffs):
    s = {0}
    for c in coeffs:
        s |= {x + c for x in s}
    return s


def safe(coeffs):
    return subset_sums(coeffs) <= {-1, 0, 1, 2}


def col_adjacency(c):
    d = len(c) - 1
    n = 1 << d
    A = [[0] * n for _ in range(n)]
    for s in range(n):
        hist = [(s >> j) & 1 for j in range(d)]
        for yn in (0, 1):
            val = c[0] * yn + sum(c[q] * hist[q - 1] for q in range(1, d + 1))
            if val in (0, 1):
                A[((s << 1) | yn) & (n - 1)][s] += 1
    return A


def col_growth(c, iters=4000):
    """PF growth of column SFT via exact adjacency eigenvalues (numpy)."""
    import numpy as np
    d = len(c) - 1
    if d == 0:
        return 2.0  # no constraint: every y free
    A = col_adjacency(c)
    ev = np.linalg.eigvals(np.array(A, dtype=float))
    lam = max(r.real for r in ev)
    return float(lam)


def col_charpoly(c):
    import sympy as sp
    d = len(c) - 1
    n = 1 << d
    A = sp.zeros(n)
    for s in range(n):
        hist = [(s >> j) & 1 for j in range(d)]
        for yn in (0, 1):
            val = c[0] * yn + sum(c[q] * hist[q - 1] for q in range(1, d + 1))
            if val in (0, 1):
                ns = ((s << 1) | yn) & (n - 1)
                A[ns, s] += 1
    return sp.factor(A.charpoly().as_expr())


print("=== S1: classify safe patterns with M = P(3^k) > 0, degree <= 7, c_0 = 1 ===")
safe_pats = []
for d in range(0, 8):
    for rest in itertools.product((-1, 0, 1), repeat=d):
        c = (1,) + rest
        if not safe(c):
            continue
        # M > 0 required: check P(3^k) > 0 for k = 1 (and k = 2 as sanity)
        ok = all(sum(v * (3 ** (i * k)) for i, v in enumerate(c)) > 0 for k in (1, 2, 3))
        if ok:
            safe_pats.append(c)
# classify: family1 {1+y^a}, family2 {1-y^a+y^b}, constant {1}
def classify(c):
    nz = [(i, v) for i, v in enumerate(c) if v != 0]
    if len(c) == 1 and c[0] == 1:
        return "trivial"
    if len(nz) == 1 and nz[0] == (0, 1):
        return "trivial"
    if len(nz) == 2 and nz[0] == (0, 1) and nz[1][1] == 1:
        return "fam1"
    if len(nz) == 3 and nz[0] == (0, 1) and nz[1][1] == -1 and nz[2][1] == 1:
        return "fam2"
    return "OTHER"
groups = {}
for c in safe_pats:
    groups.setdefault(classify(c), []).append(c)
for g, pats in sorted(groups.items()):
    print(f"  {g}: {len(pats)} patterns; examples: {pats[:6]}")

print("=== S2: column growth lambda(a,b) for fam2 patterns 1-y^a+y^b ===")
print(f"  phi = {PHI:.12f}, log3phi = {DPHI:.12f}")
results = []
eq_check = []
for b in range(2, 9):
    for a in range(1, b):
        c = tuple(1 if q in (0, b) else (-1 if q == a else 0) for q in range(b + 1))
        lam = col_growth(c)
        results.append((a, b, lam))
        mark = "phi" if abs(lam - PHI) < 1e-9 else ("VIOLATION" if lam > PHI + 1e-9 else "<phi")
        b2a = (b == 2 * a)
        if abs(lam - PHI) < 1e-9 or lam > PHI + 1e-9:
            print(f"  (a,b)=({a},{b}) b=2a:{b2a}  lambda={lam:.12f}  {mark}")
        eq_check.append((a, b, abs(lam - PHI) < 1e-9, b2a))
viol = [(a, b, lam) for a, b, lam in results if lam > PHI + 1e-9]
phi_eq = [(a, b) for a, b, e, _ in eq_check if e]
print(f"  pairs tested: {len(results)}; violations of lambda<=phi: {viol or 'NONE'}")
print(f"  lambda == phi exactly at: {phi_eq}")
expected = [(a, b) for a, b, _, b2a in eq_check if b2a]
print(f"  equality iff b==2a: {sorted(phi_eq) == sorted(expected)} (expected {expected})")

print("=== S2b: fam1 patterns 1+y^a ===")
for a in range(1, 6):
    c = tuple(1 if q in (0, a) else 0 for q in range(a + 1))
    lam = col_growth(c)
    print(f"  a={a}: lambda={lam:.12f}  |lambda-phi|={abs(lam-PHI):.2e}")

print("=== S3: cross-check dim_numeric vs log3(lambda) ===")
for (a, b) in [(1, 3), (2, 3), (1, 4), (3, 4), (2, 5), (4, 5), (1, 5), (3, 5), (1, 2), (2, 4)]:
    M = 3 ** b - 3 ** a + 1
    lam = dict(((x, y), l) for x, y, l in results)[(a, b)]
    if (a, b) not in dict(((x, y), l) for x, y, l in results):
        c = tuple(1 if q in (0, b) else (-1 if q == a else 0) for q in range(b + 1))
        lam = col_growth(c)
    dimn, _ = dt.dim_numeric(M)
    dimn = math.log(dimn) / L3
    theo = math.log(lam) / L3
    print(f"  M=3^{b}-3^{a}+1={M:<5} numeric={dimn:.12f} theory={theo:.12f} match={abs(dimn-theo)<1e-9}")

print("=== S4: exact column charpolys (new dims) for representative (a,b) ===")
for (a, b) in [(1, 3), (2, 3), (1, 4), (3, 4), (2, 5)]:
    c = tuple(1 if q in (0, b) else (-1 if q == a else 0) for q in range(b + 1))
    try:
        cp = col_charpoly(c)
        print(f"  (a,b)=({a},{b}) M={3**b-3**a+1}: charpoly = {cp}")
    except Exception as e:
        print(f"  (a,b)=({a},{b}): charpoly failed: {e}")

print("=== S5: bound push on scaled safe class M = 3^m * safe-form, m<=4 ===")
worst = 0.0
bad = []
for m in range(0, 5):
    for b in range(2, 8):
        for a in range(1, b):
            M = (3 ** m) * (3 ** b - 3 ** a + 1)
            dimn, _ = dt.dim_numeric(M)
            d = math.log(dimn) / L3 if dimn > 1 else 0.0
            worst = max(worst, d)
            if d > DPHI + 1e-9:
                bad.append((M, d))
    for a in range(1, 7):
        M = (3 ** m) * (3 ** a + 1)
        dimn, _ = dt.dim_numeric(M)
        d = math.log(dimn) / L3 if dimn > 1 else 0.0
        worst = max(worst, d)
        if d > DPHI + 1e-9:
            bad.append((M, d))
print(f"  max dim over scaled safe class (m<=4, b<=7): {worst:.12f} vs log3phi {DPHI:.12f}")
print(f"  violations: {bad or 'NONE'}")
print("DONE")
