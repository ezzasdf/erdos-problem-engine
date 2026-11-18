"""For every collision pair {u1 in D3-side, u2 = theta(u1) in D2-side}:
is psi2(u1) = flip{t, r-b} safe (admissible, c_j=1)?
Also: is psi2(u2) safe? And chi0/pairs for both sides.
Stat coverage over all tested (a,b,n).
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


def safe(v, a, b):
    for i in range(len(v)):
        zi = v[i]
        za = v[i - a] if i - a >= 0 else 0
        zb = v[i - b] if i - b >= 0 else 0
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
                t = j - g
                r = n - g
                Aprev = words(n - 1, a, b)
                img_of = {}
                for u in Aprev:
                    if cval(u, j - 1, g) or cval(u, j, g):
                        continue
                    if cval(u, j - a, g) == 0:
                        continue
                    ph = None
                    for ts in ((t,), (t, r), (t, r - b)):
                        v = flipset(u, ts)
                        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                            ph = v
                            break
                    img_of[u] = ph
                from collections import defaultdict
                grp = defaultdict(list)
                for u, im in img_of.items():
                    if im is not None:
                        grp[im].append(u)
                for im, us in grp.items():
                    if len(us) != 2:
                        continue
                    x, y = sorted(us)
                    # identify sides: D2 = chi0-safe, D3 = chi0-fail & psi1-safe
                    for u1, u2 in ((x, y), (y, x)):
                        c0_1 = flipset(u1, (t,))
                        ok0_1 = c0_1 is not None and safe(c0_1, a, b) and \
                            cval(c0_1, j, g) == 1
                        if ok0_1:
                            continue  # this is the D2 side (chi0 safe)
                        # u1 is D3-side (chi0 fails): check psi2
                        tot["d3side"] += 1
                        v = flipset(u1, (t, r - b))
                        ok = v is not None and safe(v, a, b) and \
                            cval(v, j, g) == 1
                        if ok:
                            tot["d3_psi2_ok"] += 1
                        else:
                            tot["d3_psi2_fail"] += 1
                            if len(fails) < 12:
                                fails.append(("d3", a, b, n))
                        # also psi2 of the D2 side
                        v2 = flipset(u2, (t, r - b))
                        ok2 = v2 is not None and safe(v2, a, b) and \
                            cval(v2, j, g) == 1
                        if ok2:
                            tot["d2_psi2_ok"] += 1
                        else:
                            tot["d2_psi2_fail"] += 1
    print(dict(tot))
    for f in fails:
        print("  ", f)


if __name__ == "__main__":
    main()
