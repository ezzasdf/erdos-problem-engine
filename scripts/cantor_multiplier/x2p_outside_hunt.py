# Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
# Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
# Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
"""Hunt OUTSIDE the digitwise-safe class:
  S1: phi-max violator scan  dim C(1,M) > log_3 phi  (M <= 5000)
  S2: Lemma 4.1 chain bound  lambda(a,b) <= phi  for coprime a<b <= 24
"""
import importlib.util, math, time
import numpy as np

spec = importlib.util.spec_from_file_location("dt", "x2p_dim_table.py")
dt = importlib.util.module_from_spec(spec)
spec.loader.exec_module(dt)

L3 = math.log(3.0)
PHI = (1 + 5 ** 0.5) / 2
LOG3PHI = math.log(PHI) / L3
TOL = 1e-9


def is_power3(m):
    while m % 3 == 0:
        m //= 3
    return m == 1


def reduce3(m):
    while m % 3 == 0:
        m //= 3
    return m


def is_safe_form(m):
    """m 3-power-free: m = 1, 1+3^a, or 1-3^a+3^b (b>a)."""
    if m == 1:
        return True
    if m - 1 > 0:
        t = m - 1
        while t % 3 == 0:
            t //= 3
        if t == 1:
            return True  # m = 1 + 3^a
    p = 3
    while p < m:  # 3^a < m so 1-3^a+3^b = m has 3^b = m-1+3^a > 0
        if m - 1 + p > 0:
            t = m - 1 + p
            while t % 3 == 0:
                t //= 3
            if t == 1:
                return True  # m - 1 + 3^a = 3^b
        p *= 3
    return False


def dim(M, iters=4000):
    lam, n = dt.dim_numeric(M, iters=iters)
    return math.log(lam) / L3 if lam > 1 else 0.0, n


# ---------------------------------------------------------------- S1
def s1(N=5000):
    print(f"=== S1: violator scan, 3-power-free M <= {N}, M = 1 mod 3 ===")
    t0 = time.time()
    viol, rows = [], []
    for M in range(4, N + 1, 3):  # M = 1 mod 3 (others have dim 0 or reduce)
        m = reduce3(M)
        if m == M and is_power3(M):
            continue
        if M != m:
            continue  # scaling: covered by primitive m
        d, n = dim(m)
        safe = is_safe_form(m)
        rows.append((m, d, safe, n))
        if d > LOG3PHI + 1e-6:
            viol.append((m, d, safe))
    print(f"  scanned {len(rows)} primitives in {time.time()-t0:.1f}s")
    print(f"  VIOLATORS (dim > log3phi + 1e-6): {viol if viol else 'NONE'}")
    # near-miss landscape: top 20 outside safe class
    outsiders = sorted([r for r in rows if not r[2]], key=lambda r: -r[1])[:20]
    print("  top-20 NON-safe M by dim:")
    for m, d, safe, n in outsiders:
        flag = " <== >= phi" if d > LOG3PHI + 1e-6 else ""
        print(f"    M={m:<5} dim={d:.12f}  gap_to_phi={LOG3PHI-d:.9f}  n={n}{flag}")
    # attainers (dim within 1e-6 of log3phi)
    att = [(m, d, safe) for m, d, safe, n in rows if abs(d - LOG3PHI) < 1e-6]
    print(f"  attainers of log3phi: {[(m, 'safe' if s else 'OUTSIDE') for m, d, s in att]}")
    gap = min((LOG3PHI - d) for m, d, s, n in rows if d > 0.35)
    print(f"  min gap among all dim>0.35: {gap:.9f}")
    return viol


# ------------------------------------------------------- chain SFTs
def chain_edges(a, b, cap=150000):
    """states = last b bits (LSB = z_{i-1}); constraint z_i - z_{i-a} + z_{i-b}."""
    d = b
    n = 1 << d
    seen = {0}
    frontier = [0]
    edges_r, edges_c = [], []
    while frontier:
        nf = []
        for s in frontier:
            hist = [(s >> j) & 1 for j in range(d)]
            for zn in (0, 1):
                val = zn - (hist[a - 1] if a - 1 < d else 0) + (hist[b - 1] if b - 1 < d else 0)
                if val in (0, 1):
                    ns = ((s << 1) | zn) & (n - 1)
                    edges_r.append(s)
                    edges_c.append(ns)
                    if ns not in seen:
                        seen.add(ns)
                        nf.append(ns)
        if len(seen) > cap:
            return None, None, len(seen)
        frontier = nf
    idx = {s: i for i, s in enumerate(sorted(seen))}
    r = np.array([idx[x] for x in edges_r])
    c = np.array([idx[x] for x in edges_c])
    return r, c, len(seen)


def chain_lambda(a, b, dense_max=11, iters=12000):
    """lambda of chain SFT; dense eigvals for b<=dense_max, else power it."""
    if b <= dense_max:
        n = 1 << b
        A = np.zeros((n, n))
        for s in range(n):
            hist = [(s >> j) & 1 for j in range(b)]
            for zn in (0, 1):
                val = zn - hist[a - 1] + hist[b - 1]
                if val in (0, 1):
                    A[((s << 1) | zn) & (n - 1), s] += 1
        ev = np.linalg.eigvals(A)
        return float(max(x.real for x in ev)), "dense", n
    r, c, ns = chain_edges(a, b)
    if r is None:
        return None, f"too-many-states({ns})", ns
    R = np.zeros(ns)
    R[0] = 1.0
    hist = []
    for t in range(iters):
        nxt = np.bincount(c, weights=R[r], minlength=ns)
        nr = float(np.linalg.norm(nxt))
        if nr == 0:
            return 0.0, "dead", ns
        ratio = nr / float(np.linalg.norm(R))
        hist.append(ratio)
        R = nxt / nr
        if t >= 1000 and t % 100 == 0 and abs(hist[-1] - hist[-101]) < 1e-13:
            break
    lam = hist[-1]
    drift = abs(hist[-1] - hist[-min(50, len(hist) - 1)])
    if drift > 1e-12:
        lam = hist[-1]
    return lam, f"power(ns={ns},drift={drift:.1e},t={len(hist)})", ns


def d_a(a, b):
    return a


def s2(bmax=22):
    print(f"\n=== S2: Lemma 4.1 chain bound, coprime 1 <= a < b <= {bmax} ===")
    from math import gcd
    t0 = time.time()
    worst = (9e9, None)
    viol = []
    for b in range(2, bmax + 1):
        print(f"  -- b={b} --", flush=True)
        for a in range(1, b):
            if gcd(a, b) != 1:
                continue
            lam, how, ns = chain_lambda(a, b)
            if lam is None:
                print(f"  ({a},{b}): SKIP {how}")
                continue
            gap = PHI - lam
            tag = ""
            if lam > PHI + 1e-7:
                viol.append((a, b, lam))
                tag = "  <== VIOLATION"
            if (a, b) == (1, 2):
                tag = "  (equality case)"
            elif abs(lam - PHI) < 1e-9:
                tag = "  <== EQUALITY"
            if gap < worst[0]:
                worst = (gap, (a, b, lam))
            print(f"  ({a},{b}): lambda={lam:.12f} gap={gap:.9f} [{how}]{tag}")
    print(f"  violations: {viol if viol else 'NONE'}")
    print(f"  tightest non-equality gap: {worst}")
    print(f"  ({time.time()-t0:.1f}s)")
    return viol


if __name__ == "__main__":
    v1 = s1(5000)
    v2 = s2(24)
    print("\nDONE", "VIOLATIONS:" , v1 + v2)
