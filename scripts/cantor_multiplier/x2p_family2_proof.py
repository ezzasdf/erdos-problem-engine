# Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
# Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
# Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
"""Prove dim C(1, M) = log_3(phi) for family 2: M = 3^(2k) - 3^k + 1.

Proof strategy (checked here computationally, written up in ledger):
  1. Block split: x = sum_r X_r 3^(rk), X_r = k ternary digits of x (all in {0,1}).
     M*x = sum_r Y_r 3^(rk), Y_r = X_r + X_{r-2} - X_{r-1}  (exact integer identity,
     X_{<0} = 0).
  2. M*x in Sigma  <=>  Y_r in B for all r,  B = {k-digit 0/1 ternary numbers}.
     (mod-3^k induction: |Y_r - D_r| < 3^k forces blockwise equality.)
  3. Y_r in B  <=>  digitwise: for every digit j, x_{r,j} + x_{r-2,j} - x_{r-1,j} in {0,1}.
     (mod-3 induction on w_j = d_j - eps_j in [-2,2].)
  4. Each digit column y is a binary sequence with y_{-1}=0 and NO TWO ADJACENT
     FLIPS (forbidden triples 010, 101; boundary r=1 gives exactly flip@0 => no flip@1).
     Columns independent.
  5. # such y of length n = F_{n+2}  =>  # admissible n*k-digit prefixes = F_{n+2}^k
     => growth phi^n per block => dim = log_3 phi.
"""
import math, importlib.util
spec = importlib.util.spec_from_file_location("dt", "x2p_dim_table.py")
dt = importlib.util.module_from_spec(spec); spec.loader.exec_module(dt)

L3 = math.log(3.0)
DPHI = math.log((1 + math.sqrt(5)) / 2) / L3
F = [0, 1]
for _ in range(2, 400):
    F.append(F[-1] + F[-2])


def blocks(x, k):
    out = []
    while x:
        out.append(x % 3 ** k)
        x //= 3 ** k
    return out


def digits(v):
    d = []
    while v:
        d.append(v % 3)
        v //= 3
    return d


def in_sigma(v):
    while v:
        if v % 3 > 1:
            return False
        v //= 3
    return True


print("=== Lemma 1: block identity + forward/backward equivalence ===")
for k in range(1, 4):
    M = 3 ** (2 * k) - 3 ** k + 1
    Bmax = 2 ** k  # max k-digit 0/1 number + 1
    # exhaustive over all x with up to 2k+2 digits in {0,1}
    nblocks = 4
    import itertools
    checked = 0
    for bits in itertools.product((0, 1), repeat=k * nblocks):
        x = sum(b * 3 ** i for i, b in enumerate(bits))
        X = blocks(x, k)
        ny = nblocks + 2
        while len(X) < ny:
            X.append(0)
        Y = [X[r] + (X[r - 2] if r >= 2 else 0) - (X[r - 1] if r >= 1 else 0)
             for r in range(ny)]
        ident = sum(Y[r] * 3 ** (r * k) for r in range(ny)) == M * x
        lhs = in_sigma(M * x)
        rhs = all(0 <= y < 3 ** k and in_sigma(y) for y in Y)
        assert ident, (k, x)
        assert lhs == rhs, (k, x, Y)
        checked += 1
    print(f"  k={k} M={M}: identity + equivalence OK on {checked} x's")

print("=== Lemma 2: Y_r in B <=> digitwise {0,1} column condition ===")
for k in range(1, 5):
    Bset = [sum(b * 3 ** j for j, b in enumerate(bits))
            for bits in itertools.product((0, 1), repeat=k)]
    bad = 0
    for A in Bset:
        for Bv in Bset:
            for C in Bset:
                v = C + A - Bv  # Y = X_r + X_{r-2} - X_{r-1}
                da, db, dc = digits(A), digits(Bv), digits(C)
                da += [0] * (k - len(da)); db += [0] * (k - len(db)); dc += [0] * (k - len(dc))
                lhs = 0 <= v < 3 ** k and in_sigma(v)
                rhs = all(dc[j] + da[j] - db[j] in (0, 1) for j in range(k))
                if lhs != rhs:
                    bad += 1
    print(f"  k={k}: digitwise factorization {'OK' if bad == 0 else f'MISMATCH {bad}'}")

print("=== Lemma 4/5: per-column count = F_{n+2}; total = F_{n+2}^k; dim ===")
for k in range(1, 4):
    M = 3 ** (2 * k) - 3 ** k + 1
    # per-column: sequences y_{-1}=0, y_0..y_{n-1}, no two adjacent flips
    def col_count(n):
        c = 0
        for bits in itertools.product((0, 1), repeat=n):
            y = [0] + list(bits)
            flips = [y[i] != y[i - 1] for i in range(1, n + 1)]
            if all(not (flips[i] and flips[i + 1]) for i in range(len(flips) - 1)):
                c += 1
        return c
    ok = all(col_count(n) == F[n + 2] for n in range(1, 12))
    print(f"  k={k}: per-column count = F_(n+2) for n=1..11: {ok}")

print("=== End-to-end: automaton leaves(nk) == F_(n+2)^k, dim = log_3 phi ===")
for k in range(1, 4):
    M = 3 ** (2 * k) - 3 ** k + 1
    n = 6
    cnt = dt.count_streams(M, n * k)
    expect = F[n + 2] ** k
    print(f"  k={k} M={M}: #admissible ({n}k={n*k} digits) = {cnt}, F_{n+2}^{k} = {expect}, match={cnt == expect}")

print("=== dim via numeric vs log_3 phi ===")
for k in range(1, 7):
    M = 3 ** (2 * k) - 3 ** k + 1
    lam, nn = dt.dim_numeric(M)
    d = math.log(lam) / L3 if lam > 1 else 0.0
    print(f"  k={k} M={M:<7} dim={d:.12f}  |dim-log3phi|={abs(d-DPHI):.2e}")
print("DONE")
