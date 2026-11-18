"""Lemma 4.1: greedy layered injection with image exclusion (collision-free).

Branch 1: u in G, c_{j-a}=0  -> flip j               (D-part)
Branch 2: u in G, c_{j-a}=1, chi0(u) safe             chi0 = flip{j-g}
Branch 3: + psi1(u) safe and psi1(u) not in I2        psi1 = flip{j-g, n-g}
Branch 4: + psi2(u) safe and psi2(u) not in I2 u I3   psi2 = flip{j-g, n-g-b}
Goal: total + injective + images in Z for all tested (a,b,n).
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
    fail = []
    for a in range(2, 8):
        for b in range(a + 1, 11):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a + 1, 17):
                j = n - a
                Aprev = words(n - 1, a, b)
                G = [u for u in Aprev
                     if cval(u, j - 1, g) == 0 and cval(u, j, g) == 0]
                images = {}
                I2 = set()
                I3 = set()
                I4 = set()
                # pass order matters: branch2 first (its images fix exclusion)
                for u in G:
                    if cval(u, j - a, g) == 0:
                        v = flipset(u, (j,))
                        assert v is not None and safe(v, a, b) and \
                            cval(v, j, g) == 1, (a, b, n, u)
                        images[u] = v
                        tot["b1"] += 1
                for u in G:
                    if u in images:
                        continue
                    t = j - g
                    v = flipset(u, (t,)) if t >= 0 else None
                    if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                        images[u] = v
                        I2.add(v)
                        tot["b2"] += 1
                for u in G:
                    if u in images:
                        continue
                    t = j - g
                    v = flipset(u, (t, n - g))
                    if v is not None and safe(v, a, b) and \
                       cval(v, j, g) == 1 and v not in I2:
                        images[u] = v
                        I3.add(v)
                        tot["b3"] += 1
                for u in G:
                    if u in images:
                        continue
                    t = j - g
                    v = flipset(u, (t, n - g - b))
                    if v is not None and safe(v, a, b) and \
                       cval(v, j, g) == 1 and v not in I2 and v not in I3:
                        images[u] = v
                        I4.add(v)
                        tot["b4"] += 1
                missing = [u for u in G if u not in images]
                if missing:
                    tot["uncovered"] += len(missing)
                    fail.append(("uncov", a, b, n, missing[0]))
                    continue
                imgs = list(images.values())
                if len(set(imgs)) != len(imgs):
                    tot["dup"] += 1
                    fail.append(("dup", a, b, n, None))
                for v in imgs:
                    if not safe(v, a, b) or cval(v, j, g) != 1:
                        tot["badimg"] += 1
                # count check |G| <= |Z|
                Zc = sum(1 for u in Aprev if cval(u, j, g) == 1)
                if len(G) > Zc:
                    tot["countviol"] += 1
                    fail.append(("cnt", a, b, n, None))
    print(dict(tot))
    for f in fail[:12]:
        print("  ", f)


if __name__ == "__main__":
    main()
