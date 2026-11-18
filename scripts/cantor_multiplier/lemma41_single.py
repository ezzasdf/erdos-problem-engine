"""Lemma 4.1: is there a single fixed 2-flip set S (per a,b,n) with
u xor S in A_{n-1} for ALL u in G n E, landing in Z?

Candidate S = {t, r} with t in {j-g, j} (must toggle c_j), r arbitrary.
For each (a,b,n): intersect good sets over all u in G n E; look for formula.
"""
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
    for i in range(n):
        zi = w[i]
        za = w[i - a] if i - a >= 0 else 0
        zb = w[i - b] if i - b >= 0 else 0
        if not (0 <= zi - za + zb <= 1):
            return False
    return True


def main():
    results = []
    for a in range(2, 7):
        for b in range(a + 1, 10):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a + 1, 16):
                j = n - a
                Eset = []
                for u in words(n - 1, a, b):
                    if cval(u, j - 1, g) or cval(u, j, g):
                        continue
                    if cval(u, j - a, g) == 1:
                        Eset.append(u)
                if not Eset:
                    continue
                common = None
                for u in Eset:
                    good = set()
                    for t in (j - g, j):
                        if t < 0:
                            continue
                        for r in range(n - 1):
                            if r == t:
                                continue
                            v = flipset(u, (t, r))
                            if v is not None and safe(v, a, b) and \
                               cval(v, j, g) == 1:
                                good.add((t, r))
                    common = good if common is None else (common & good)
                results.append((a, b, n, g, j, common))
                print(f"(a,b)=({a},{b}) n={n} |E|={len(Eset)} "
                      f"common size={len(common)}: "
                      f"{sorted(common)[:8]}")
    # formula hunt: for each common set, check candidate formulas
    print("\nformula coverage:")
    formulas = {
        "(j-g, n-g)": lambda a, b, n, j, g: (j - g, n - g),
        "(j-g, n-g-b)": lambda a, b, n, j, g: (j - g, n - g - b),
        "(j, n-g)": lambda a, b, n, j, g: (j, n - g),
        "(j-g, j-a)": lambda a, b, n, j, g: (j - g, j - a),
        "(j-g, n-1)": lambda a, b, n, j, g: (j - g, n - 2),
        "(j, j-b)": lambda a, b, n, j, g: (j, j - b),
        "(j-g, g)": lambda a, b, n, j, g: (j - g, g),
    }
    for name, f in formulas.items():
        hit = miss = skipped = 0
        for (a, b, n, g, j, common) in results:
            s = f(a, b, n, j, g)
            if s[1] < 0 or s[1] > n - 2:
                skipped += 1
                continue
            if s in common:
                hit += 1
            else:
                miss += 1
        print(f"    {name}: hit {hit}, miss {miss}, skipped {skipped}")


if __name__ == "__main__":
    main()
