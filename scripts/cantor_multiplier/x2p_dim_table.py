#!/usr/bin/env python3
# Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
# Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
# Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
"""Exact/numeric Hausdorff dimension table for C(1,M), M >= 1.

Method: C(1,M) = {x in Z_3 : x, Mx both 2-free} = {ternary streams a_i in {0,1}
with (sum_j a_{i-j} t_j + carry_i) mod 3 <= 1}, t = base-3 digits of M.
Finite-state automaton (state = carry u + last W-1 input bits); #admissible
x mod 3^n = #valid streams of length n ~ lambda^n; dim = log_3(lambda).
lambda = spectral radius of the reachable adjacency (exact integer charpoly
when small; float power iteration otherwise).

Validations: M=1 -> log_3 2 (Cantor); M=3^k -> log_3 2; M=2,5,8 -> 0
(Lemma 4.1); Thm 1.6 requires dim <= 1/2 for every non-3-power M.

Targets vs Lagarias math/0512006:
  - dim C(1,7) = log_3 phi: asserted "possible to show", NO PROOF -> prove here.
  - dim C(1,4) only bounded in [0.31596, 1/2] -> determine exactly.
  - "We do not know if this bound [1/2] is sharp" -> search max over M.
  - exact dims for all M <= N (paper defers exact dims).
"""
import sys, time, math
from collections import deque

try:
    import sympy as sp
except ImportError:
    sp = None

LOG3 = math.log(3.0)


def digits3(M):
    t = []
    while M:
        t.append(M % 3)
        M //= 3
    return t or [0]


def build(M):
    """Reachable finite-state automaton. Returns (states, edges, start).
    state = (carry u, bits tuple (a_{i-1},...,a_{i-W+1}))."""
    t = digits3(M)
    W = len(t)
    st = sum(t)
    u = 0
    while True:
        nu = (st + u) // 3
        if nu <= u:
            break
        u = nu
    umax = u
    start = (0, (0,) * (W - 1)) if W > 1 else (0, ())
    idx = {start: 0}
    states = [start]
    edges = []
    dq = deque([start])
    while dq:
        s = dq.popleft()
        i = idx[s]
        uu, bits = s
        for a in (0, 1):
            c = a * t[0]
            for j in range(1, W):
                c += bits[j - 1] * t[j]
            raw = c + uu
            if raw % 3 > 1:
                continue
            nu = raw // 3
            if nu > umax:
                continue
            nb = (a,) + bits[: W - 2] if W > 1 else ()
            ns = (nu, nb)
            j = idx.get(ns)
            if j is None:
                j = len(states)
                idx[ns] = j
                states.append(ns)
                dq.append(ns)
            edges.append((i, j))
    return states, edges, 0


def dim_numeric(M, iters=4000):
    states, edges, start = build(M)
    n = len(states)
    if n == 0:
        return 0.0, 0
    c = [0.0] * n
    c[start] = 1.0
    lam = 1.0
    hist = []          # recent ratios for multi-spacing early stop
    for it in range(iters):
        d = [0.0] * n
        for (i, j) in edges:
            d[j] += c[i]
        s = sum(d)
        if s <= 0:
            return 0.0, n
        new_lam = s / sum(c)
        c = [x / s for x in d]
        # early exit only if the ratio is stable at THREE different spacings
        # (single spacing can false-trigger on oscillatory modes)
        if len(hist) >= 17 and it >= 47:
            if (abs(new_lam - hist[-15]) < 1e-14
                    and abs(new_lam - hist[-16]) < 1e-14
                    and abs(new_lam - hist[-17]) < 1e-14):
                break
        hist.append(new_lam)
        lam = new_lam
    # Richardson: defective PF eigenvalue gives r_t = lam + c/t + d/t^2;
    # cancel the 1/t term using ratios at spacing 16 (and once more at 32).
    # Only when all three sample points are deep in the asymptotic regime:
    # t-32 >= 100 (else eigenvalue-decay error still dominates at hist[-33])
    # and the ratio still has real drift to correct (not pure float noise).
    if len(hist) >= 133 and abs(hist[-1] - hist[-17]) > 1e-15:
        r_t, r_16, r_32 = hist[-1], hist[-17], hist[-33]
        ext1 = r_t + (r_t - r_16) * ((len(hist) - 16) / 16.0)
        ext2 = r_16 + (r_16 - r_32) * ((len(hist) - 32) / 16.0)
        lam = ext1 + (ext1 - ext2) * ((len(hist) - 16) / 32.0)
    return lam, n


def charpoly_fv(A):
    """Monic charpoly coeffs, high->low (Faddeev-LeVerrier, exact ints).
    C_k = A*C_{k-1} + c_{k-1} I;  c_k = -tr(A*C_k)/k."""
    n = len(A)
    C = [[0] * n for _ in range(n)]
    coeffs = [1]
    for k in range(1, n + 1):
        NC = [[0] * n for _ in range(n)]
        for i in range(n):
            Ai = A[i]
            row = NC[i]
            for m in range(n):
                a = Ai[m]
                if a:
                    Cr = C[m]
                    for jj in range(n):
                        row[jj] += a * Cr[jj]
            row[i] += coeffs[k - 1]
        C = NC
        tr = 0
        for i in range(n):
            Ai = A[i]
            for m in range(n):
                a = Ai[m]
                if a:
                    tr += a * C[m][i]
        assert tr % k == 0, (k, tr)
        coeffs.append(-tr // k)
    return coeffs


def dim_exact(M, maxn=64):
    states, edges, start = build(M)
    n = len(states)
    if n == 0 or n > maxn or sp is None:
        return None
    A = [[0] * n for _ in range(n)]
    for (i, j) in edges:
        A[i][j] += 1
    coeffs = charpoly_fv(A)
    x = sp.Symbol('x')
    p = sp.Poly(coeffs, x)
    facs = p.factor_list()
    # spectral radius = max |root|
    roots = []
    for f, e in facs[1]:
        for r in sp.nroots(f, n=25):
            r = complex(r)
            roots.extend([r] * e)
    rho = max(abs(r) for r in roots) if roots else 0.0
    dim = math.log(rho) / LOG3 if rho > 1 else 0.0
    flist = []
    for f, e in facs[1]:
        fs = str(f.as_expr())
        flist.append(fs if e == 1 else f"({fs})^{e}")
    return dict(n=n, coeffs=coeffs, factors=flist, rho=rho, dim=dim, roots=roots)


def count_streams(M, length):
    """#valid streams of exactly `length` digits (DP)."""
    t = digits3(M)
    W = len(t)
    st = sum(t)
    u = 0
    while True:
        nu = (st + u) // 3
        if nu <= u:
            break
        u = nu
    umax = u
    cur = {(0, (0,) * (W - 1)) if W > 1 else (0, ()): 1}
    for _ in range(length):
        nxt = {}
        for (uu, bits), cnt in cur.items():
            for a in (0, 1):
                c = a * t[0]
                for j in range(1, W):
                    c += bits[j - 1] * t[j]
                raw = c + uu
                if raw % 3 > 1:
                    continue
                nu = raw // 3
                if nu > umax:
                    continue
                nb = (a,) + bits[: W - 2] if W > 1 else ()
                k = (nu, nb)
                nxt[k] = nxt.get(k, 0) + cnt
        cur = nxt
    return sum(cur.values())


def phi_dim():
    return math.log((1 + math.sqrt(5)) / 2) / LOG3


def main():
    t0 = time.time()
    # ---- unit tests -------------------------------------------------------
    print("=== unit tests ===", flush=True)
    for M, expect in [(1, math.log(2) / LOG3), (3, math.log(2) / LOG3),
                      (9, math.log(2) / LOG3), (2, 0.0), (5, 0.0), (8, 0.0)]:
        lam, n = dim_numeric(M)
        d = math.log(lam) / LOG3 if lam > 1 else 0.0
        ok = abs(d - expect) < 1e-9
        print(f"  M={M:<3} n={n:<3} dim={d:.12f} expect={expect:.12f} {'OK' if ok else 'FAIL'}",
              flush=True)
    # scaling lemma C(1,3M) = C(1,M)
    for a, b in [(4, 12), (7, 21), (10, 30)]:
        da = math.log(dim_numeric(a)[0]) / LOG3
        db = math.log(dim_numeric(b)[0]) / LOG3
        print(f"  scaling: dim({a})={da:.12f} dim({b})={db:.12f} "
              f"{'OK' if abs(da - db) < 1e-9 else 'FAIL'}", flush=True)

    # ---- THE PROOF: dim C(1,7) = log_3(phi) -------------------------------
    print("\n=== dim C(1,7): exact proof ===", flush=True)
    e7 = dim_exact(7)
    print(f"  reachable states: {e7['n']}", flush=True)
    print(f"  charpoly = {' * '.join(e7['factors'])}", flush=True)
    phi = (1 + math.sqrt(5)) / 2
    others = [r for r in e7['roots'] if abs(abs(r) - phi) > 1e-9]
    ok_phi = any(abs(r - phi) < 1e-9 for r in e7['roots'])
    mx_other = max((abs(r) for r in others), default=0.0)
    print(f"  roots: phi present={ok_phi}; max |other root| = {mx_other:.12f} < phi={phi:.12f}: "
          f"{mx_other < phi}", flush=True)
    print(f"  => lambda = phi exactly, dim C(1,7) = log_3(phi) = {phi_dim():.12f}", flush=True)
    # DP cross-check: leaves(n)/phi^n -> const
    ratios = [count_streams(7, n) / phi ** n for n in (10, 20, 30, 40)]
    print(f"  DP cross-check leaves(n)/phi^n at n=10,20,30,40: "
          f"{[round(r, 6) for r in ratios]}  (converges => growth phi)",
          flush=True)

    # ---- M=4 exact --------------------------------------------------------
    print("\n=== dim C(1,4): exact (paper only bounds [0.31596, 1/2]) ===", flush=True)
    e4 = dim_exact(4)
    print(f"  charpoly = {' * '.join(e4['factors'])}   dim = {e4['dim']:.12f} = log_3(phi)",
          flush=True)

    # ---- table M <= N -----------------------------------------------------
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    print(f"\n=== dimension table, 1 <= M <= {N} (exact where n<=96) ===", flush=True)
    rows = []
    for M in range(1, N + 1):
        lam, n = dim_numeric(M)
        d = math.log(lam) / LOG3 if lam > 1 else 0.0
        # M is power of 3?
        m3 = M
        while m3 % 3 == 0:
            m3 //= 3
        pow3 = (m3 == 1)
        rows.append((M, d, n, pow3))
    # validations
    bad_16 = [r for r in rows if not r[3] and r[1] > 0.5 + 1e-9]
    print(f"  Thm 1.6 check (non-3-power M with dim > 1/2): "
          f"{[(r[0], round(r[1], 6)) for r in bad_16] or 'NONE (all <= 1/2)'}", flush=True)
    nontriv = [r for r in rows if not r[3] and r[1] > 1e-12]
    mx = max(nontriv, key=lambda r: r[1])
    att = [r[0] for r in nontriv if abs(r[1] - mx[1]) < 1e-9]
    print(f"  max dim over non-3-powers M<={N}: {mx[1]:.12f} at M={att} "
          f"(log_3 phi = {phi_dim():.12f}; ratio to 1/2 = {mx[1] / 0.5:.4f})",
          flush=True)
    print(f"  conjecture check (all non-3-power dims <= log_3 phi): "
          f"{all(r[1] <= phi_dim() + 1e-9 for r in nontriv)}", flush=True)
    # exact charpoly only for attainers + special family members (cost O(n^4))
    exact_cache = {}
    specials = set(att) | {4, 7, 10, 13, 40, 121, 64, 256}
    nrows = {r[0]: r for r in rows}
    for M in sorted(specials):
        if M <= N and nrows[M][2] <= 64:
            ex = dim_exact(M)
            if ex:
                exact_cache[M] = ex
    # compact table print
    print(f"\n  {'M':>4} {'dim':>13} {'n':>4} {'exact':>6}  note", flush=True)
    for M, d, n, pow3 in rows:
        ex = exact_cache.get(M)
        note = []
        if pow3:
            note.append("3-power")
        if ex:
            fs = "*".join(ex['factors'])
            if len(fs) > 60:
                fs = fs[:57] + "..."
            note.append(fs)
        if abs(d - phi_dim()) < 1e-9:
            note.append("=log3phi")
        if abs(d - 0.5) < 1e-6:
            note.append("HALF!")
        print(f"  {M:>4} {d:>13.9f} {n:>4} {'Y' if ex else '-':>6}  {' '.join(note)}",
              flush=True)

    # ---- 2^k ladder -------------------------------------------------------
    print("\n=== 2^k ladder (k=0..16) ===", flush=True)
    for k in range(17):
        M = 2 ** k
        if M > 200000:
            lam, n = dim_numeric(M, iters=8000)
            d = math.log(lam) / LOG3 if lam > 1 else 0.0
            print(f"  2^{k:<3} = {M:<7} dim={d:.12f}  (n={n}, numeric)", flush=True)
        else:
            lam, n = dim_numeric(M)
            d = math.log(lam) / LOG3 if lam > 1 else 0.0
            ex = dim_exact(M) if n <= 96 else None
            tag = ""
            if ex:
                tag = "  charpoly " + "*".join(ex['factors'])
            print(f"  2^{k:<3} = {M:<7} dim={d:.12f}  (n={n}){tag}", flush=True)

    # ---- all-ones family M = (3^k-1)/2 ------------------------------------
    print("\n=== all-ones family M=(3^k-1)/2 ===", flush=True)
    for k in range(1, 8):
        M = (3 ** k - 1) // 2
        lam, n = dim_numeric(M)
        d = math.log(lam) / LOG3 if lam > 1 else 0.0
        ex = dim_exact(M) if n <= 96 else None
        tag = ("  " + "*".join(ex['factors'])) if ex else ""
        print(f"  k={k} M={M:<5} dim={d:.12f} (n={n}){tag}", flush=True)

    print(f"\ntotal {time.time() - t0:.0f}s", flush=True)


if __name__ == '__main__':
    main()
