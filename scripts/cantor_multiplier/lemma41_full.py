"""Lemma 4.1: comprehensive verification of the full injection phi: G -> Z.

G = {u in A_{n-1} : (c_{j-1}, c_j) = (0,0)}   (two consecutive free positions)
Z = {u in A_{n-1} : c_j = 1}                   (position n forced)
Target: |G| <= |Z|  (=> B(n) <= N(n-1) => Fibonacci recurrence => lambda <= phi)

Branches:
  1. u in G, c_{j-a}=0  : flip bit j               (proven safe)
  2. u in G, c_{j-a}=1  : flip bit j-g             (safe iff s_{n-b}=1 and not allEqual(n-g))
  3. else: flip {j-g, n-g}                          (repair of allEqual(n-g))
  4. else: flip {j-g, n-g-b}                        (second repair)
Check totality, landing in Z, injectivity, and s_{n-b} on G with c_{j-a}=1.
"""
from itertools import product
from math import gcd
from collections import Counter


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
    tot = Counter()
    fails = []
    for a in range(2, 8):
        for b in range(a + 1, 11):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a + 1, 17):
                j = n - a
                Aprev = words(n - 1, a, b)
                # predicate checks
                for u in Aprev:
                    if cval(u, j - 1, g) or cval(u, j, g):
                        continue  # not in G
                    tot["G"] += 1
                    if cval(u, j - a, g) == 0:
                        # branch 1
                        v = flipset(u, (j,))
                        if v is None or not safe(v, a, b) or cval(v, j, g) != 1:
                            tot["b1_fail"] += 1
                            fails.append(("b1", a, b, n, u))
                        else:
                            tot["b1"] += 1
                        continue
                    # c_{j-a} = 1: record s_{n-b}
                    t = j - g
                    st = (u[n - b - a] if n - b - a >= 0 else 0) == \
                         (u[n - b - b] if n - b - b >= 0 else 0)
                    tot["E"] += 1
                    if not st:
                        tot["E_not_st"] += 1
                    branch = None
                    if t >= 0:
                        v = flipset(u, (t,))
                        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                            branch = "b2"
                    if branch is None:
                        v = flipset(u, (t, n - g))
                        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                            branch = "b3"
                    if branch is None:
                        v = flipset(u, (t, n - g - b))
                        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                            branch = "b4"
                    if branch is None:
                        tot["uncovered"] += 1
                        fails.append(("none", a, b, n, u))
                    else:
                        tot[branch] += 1

                # full injection check per (a,b,n)
                G, Z = [], []
                images = []
                ok = True
                for u in Aprev:
                    if cval(u, j - 1, g) or cval(u, j, g):
                        continue
                    G.append(u)
                    ph = None
                    if cval(u, j - a, g) == 0:
                        ph = flipset(u, (j,))
                    else:
                        t = j - g
                        for ts in ((t,), (t, n - g), (t, n - g - b)):
                            v = flipset(u, ts)
                            if v is not None and safe(v, a, b) and \
                               cval(v, j, g) == 1:
                                ph = v
                                break
                    if ph is None:
                        ok = False
                        break
                    images.append(ph)
                if not ok:
                    continue
                if len(set(images)) != len(images):
                    tot["dup_images"] += 1
                    fails.append(("dup", a, b, n, None))
                for ph in images:
                    if cval(ph, j, g) != 1 or not safe(ph, a, b):
                        tot["bad_image"] += 1
                if len(G) > sum(1 for u in Aprev
                                if cval(u, j, g) == 1):
                    tot["count_violation"] += 1
                    fails.append(("count", a, b, n, None))
    print(dict(tot))
    for f in fails[:15]:
        print("  fail:", f)


if __name__ == "__main__":
    main()
