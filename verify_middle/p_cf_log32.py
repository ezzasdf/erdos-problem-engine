#!/usr/bin/env python3
"""Continued fraction of log_3(2) and the probability -> pointwise connection.

The density law P(f>=L) = C*(2/3)^L predicts the exception count
    e_L(N) = #{n < N : f(n) >= L} = N*P(f>=L) + O(N*2^L*D*_N)
(Koksma; S_L is a union of 2^{L-1} intervals, total variation 2^L).
A pointwise bound max_{n<N} f(n) < L is exactly e_L(N) = 0.  This script
(a) computes the continued fraction of alpha = log_3(2) (the object that
    controls D*_N),
(b) validates the standard bound D*_N <= (sum_{q_i<=N} q_i)/(N+1) by brute
    force,
(c) quantifies the Obstruction Lemma: the band N*2^L*D*_N >= 2^{L-1} >= 1 for
    every L >= 1, so the density law can never certify a pointwise bound.
Python stdlib only (decimal). Run from repo root.
"""

import csv
import math
from decimal import Decimal, getcontext

getcontext().prec = 240

C_EXACT = Decimal("1.1147647951")  # P(f>=L)/(2/3)^L, converged by L ~ 10 (p_first2.py)


def ln_dec(x, iters=400):
    """ln(x) = 2*atanh((x-1)/(x+1)); fallback if Decimal.ln is unavailable."""
    z = (Decimal(x) - 1) / (Decimal(x) + 1)
    z2 = z * z
    s = Decimal(0)
    zk = z
    for k in range(1, iters + 1):
        s += zk / (2 * k - 1)
        zk *= z2
    return 2 * s


def log32():
    if hasattr(Decimal, "ln"):
        return Decimal(2).ln() / Decimal(3).ln()
    return ln_dec(2) / ln_dec(3)


def cf(x, nterms=44):
    """Partial quotients and convergents: p[k]/q[k] = [a0; a1, ..., ak]."""
    a, p, q = [], [], []
    pm2, pm1 = 0, 1  # p_{-2}, p_{-1}
    qm2, qm1 = 1, 0  # q_{-2}, q_{-1}
    cur = x
    for _ in range(nterms):
        ai = int(cur)
        a.append(ai)
        pi = ai * pm1 + pm2
        qi = ai * qm1 + qm2
        p.append(pi)
        q.append(qi)
        pm2, pm1, qm2, qm1 = pm1, pi, qm1, qi
        frac = cur - ai
        if frac == 0:
            break
        cur = Decimal(1) / frac
    return a, p, q  # p_k = p[k], q_k = q[k]; q_0 = 1


def kmax(N, q):
    k = 0
    while k + 1 < len(q) and q[k + 1] <= N:
        k += 1
    return k


def dbound(N, q):
    k = kmax(N, q)
    return sum(q[:k + 1]) / (Decimal(N) + 1)


def star_discrepancy(N, alpha):
    pts = sorted((alpha * Decimal(n)) % Decimal(1) for n in range(N))
    m = Decimal(N)
    best = Decimal(0)
    count = 0
    for x in pts:
        dev = abs(Decimal(count) / m - x)
        if dev > best:
            best = dev
        count += 1
    dev = abs(Decimal(count) / m - Decimal(1))
    if dev > best:
        best = dev
    return best


def max_gap(N, alpha):
    pts = sorted((alpha * Decimal(n)) % Decimal(1) for n in range(N))
    g = pts[0]
    for i in range(1, N):
        gap = pts[i] - pts[i - 1]
        if gap > g:
            g = gap
    gap = Decimal(1) - pts[-1]
    return gap if gap > g else g


def P_exact(L):
    total = 0.0
    for m in range(2 ** (L - 1)):
        t = 1.0
        for i in range(1, L):
            if (m >> (L - 1 - i)) & 1:
                t += 3.0 ** (-i)
        total += math.log((t + 3.0 ** (1 - L)) / t, 3)
    return total


def main():
    alpha = log32()
    a, p, q = cf(alpha)

    print("== alpha = log_3(2), first 60 digits ==")
    s = str(alpha)
    print("   " + s[:62])
    print(f"   precision context: {getcontext().prec} digits")

    print("\n== continued fraction: a_i and denominators q_i ==")
    print(f"{'i':>3} {'a_i':>4} {'q_i':>25}")
    for i in range(min(len(a), 44)):
        print(f"{i:>3} {a[i]:>4} {q[i]:>25}")

    print("\n== Legendre self-check: |alpha - p_k/q_k| < 1/q_k^2 (k = 1..20) ==")
    ok = True
    for k in range(1, 21):
        err = abs(alpha - Decimal(p[k]) / Decimal(q[k]))
        bound = Decimal(1) / (Decimal(q[k]) * Decimal(q[k]))
        ok = ok and err < bound
    print(f"   holds for k=1..20: {ok}")

    print("\n== validate D*_N <= (sum_{q_i<=N} q_i)/(N+1) by brute force ==")
    print(f"{'N':>5} {'k':>3} {'sum_q':>12} {'D*':>12} {'bound':>12} {'D*/bound':>9}")
    worst = 0.0
    held = True
    for N in range(100, 2001, 100):
        D = star_discrepancy(N, alpha)
        b = dbound(N, q)
        ratio = D / b
        held = held and D <= b
        worst = max(worst, float(ratio))
        print(f"{N:>5} {kmax(N, q):>3} {sum(q[:kmax(N, q)+1]):>12} "
              f"{float(D):12.6f} {float(b):12.6f} {float(ratio):9.3f}")
    print(f"   bound holds on the grid: {held}; worst ratio: {worst:.3f}")

    print("\n== obstruction table: mean vs band at the certified maxima ==")
    records = {10**6: 36, 10**7: 40, 10**9: 50}
    print(f"{'N':>10} {'k':>3} {'q_k':>12} {'q_{k+1}':>14} {'D*_N':>12} "
          f"{'L':>4} {'mean':>8} {'band':>10}")
    for N, L in records.items():
        k = kmax(N, q)
        D = dbound(N, q)
        mean = N * float(C_EXACT) * (2.0 / 3.0) ** L
        band = N * (2 ** L) * float(D)
        print(f"{N:>10} {k:>3} {q[k]:>12} {q[k+1]:>14} {float(D):12.3e} "
              f"{L:>4} {mean:8.3f} {band:10.2e}")

    print("\n== predictive vs certified at N = 10^6 (events grid) ==")
    print(f"{'L':>3} {'measured':>9} {'predicted':>10} {'z':>6} {'band':>10}")
    with open("verify_middle/first2_events.csv") as f:
        for r in csv.DictReader(f):
            L = int(r["L"])
            n = int(r["N"])
            pm = float(r["P_f_ge_L"])
            pe = P_exact(L) if L <= 20 else float(C_EXACT) * (2.0 / 3.0) ** L
            se = math.sqrt(pe * (1 - pe) / n) if pe > 0 else 0.0
            z = (pm - pe) / se if se > 0 else 0.0
            band = n * (2 ** L) * float(dbound(n, q))
            print(f"{L:>3} {n*pm:9.1f} {n*pe:10.1f} {z:6.2f} {band:10.2e}")

    print("\n== the obstruction in one number (universal, no CF needed) ==")
    print("   D*_N >= 1/(2N) for any N points  =>  band = N*2^L*D*_N >= 2^{L-1} >= 1.")
    print("   The counting bound e_L(N) <= N*P(f>=L) + band can never be < 1")
    print("   for L >= 1, so it can never certify e_L(N) = 0 (a pointwise bound).")


if __name__ == "__main__":
    main()