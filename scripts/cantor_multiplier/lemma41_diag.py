"""Lemma 4.1: diagnose the 7 hard cases where {j-g, n-g} and {j, n-g} fail."""
from itertools import product
from math import gcd
from collections import defaultdict


def direct_ok(w, a, b):
    n = len(w)
    for i in range(n):
        zi = w[i]
        za = w[i - a] if i - a >= 0 else 0
        zb = w[i - b] if i - b >= 0 else 0
        if not (0 <= zi - za + zb <= 1):
            return False
    return True


def words(n, a, b):
    return [w for w in product((0, 1), repeat=n) if direct_ok(w, a, b)]


def cval(w, m, g):
    zj = w[m] if 0 <= m < len(w) else 0
    zg = w[m - g] if m - g >= 0 else 0
    return zj ^ zg


def flipset(w, ts):
    v = list(w)
    for t in ts:
        if not (0 <= t < len(v)):
            return None
        v[t] ^= 1
    return tuple(v)


def safe(w, a, b):
    n = len(w)
    bad = []
    for i in range(n):
        zi = w[i]
        za = w[i - a] if i - a >= 0 else 0
        zb = w[i - b] if i - b >= 0 else 0
        if not (0 <= zi - za + zb <= 1):
            bad.append(i)
    return bad


def main():
    hard = []
    for a in range(2, 7):
        for b in range(a + 1, 10):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a, 15):
                j = n - a
                for u in words(n - 1, a, b):
                    if cval(u, j - 1, g) or cval(u, j, g):
                        continue
                    if cval(u, j - a, g) == 0:
                        continue
                    ok = False
                    for t in (j, j - g):
                        if t < 0:
                            continue
                        v = flipset(u, (t,))
                        if v and not safe(v, a, b) and False:
                            ok = True
                        if v and safe(v, a, b) == [] and cval(v, j, g) == 1:
                            ok = True
                    if not ok:
                        hard.append((a, b, n, g, j, u))
    fails = []
    for (a, b, n, g, j, u) in hard:
        r = n - g
        worked = False
        for t in (j - g, j):
            v = flipset(u, (t, r))
            if v is not None and safe(v, a, b) == [] and cval(v, j, g) == 1:
                worked = True
        if not worked:
            fails.append((a, b, n, g, j, u, r))
    print(f"failures of r=n-g: {len(fails)}")
    for (a, b, n, g, j, u, r) in fails:
        print(f"\n  a={a} b={b} n={n} g={g} j={j} r={r} u={u}")
        for t in (j - g, j):
            v = flipset(u, (t, r))
            if v is None:
                print(f"    t={t}: out of range")
                continue
            brk = safe(v, a, b)
            print(f"    t={t}: broken={brk} c_j'={cval(v, j, g)}")
        # what DOES work for this u?
        good = []
        for t in (j - g, j):
            if t < 0:
                continue
            for rr in range(n - 1):
                if rr == t:
                    continue
                v = flipset(u, (t, rr))
                if v and safe(v, a, b) == [] and cval(v, j, g) == 1:
                    good.append((t, rr))
        print(f"    working (t,r): {good[:14]}{'...' if len(good) > 14 else ''}")


if __name__ == "__main__":
    main()
