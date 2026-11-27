# Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
# Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
# Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
"""Lemma 4.1: test the double-flip injection psi: (c_{j-1},c_j)=(0,0) -> (1,1).

psi flips bits t1 = j-1-g and t2 = j-g (both must be >=0, i.e. n >= b+1).
Effect: c_{j-1} and c_j both toggle; c_{j-g}, c_{j-1-g} also toggle (ignored).
Goal: psi safe on X = {(0,0)}  =>  |(0,0)| <= |(1,1)|  => N_00 <= N_11
      => N_00 <= N_01 + N_11  => B(n) <= N(n-1)  => Fibonacci recurrence.
Also test single flip_{j-g} and flip_j coverage of X.
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


def apply_flips(w, ts):
    v = list(w)
    for t in ts:
        if t < 0 or t >= len(v):
            return None
        v[t] ^= 1
    return tuple(v)


def safe(w, a, b):
    n = len(w)
    return all(0 <= (w[i] - (w[i - a] if i - a >= 0 else 0)
                     - (-(w[i - b] if i - b >= 0 else 0))) <= 1
               for i in range(n))


def safe2(w, a, b):
    n = len(w)
    for i in range(n):
        zi = w[i]
        za = w[i - a] if i - a >= 0 else 0
        zb = w[i - b] if i - b >= 0 else 0
        if not (0 <= zi - za + zb <= 1):
            return False
    return True


def main():
    print("[P] psi = flip{j-1-g, j-g} on X={(c_{j-1},c_j)=(0,0)}: "
          "safe? image in (1,1)? injective?")
    tot = Counter()
    fails = []
    for a in range(2, 8):
        for b in range(a + 1, 12):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a, 17):
                j = n - a
                t1, t2 = j - 1 - g, j - g
                Aprev = words(n - 1, a, b)
                X = [u for u in Aprev
                     if cval(u, j - 1, g) == 0 and cval(u, j, g) == 0]
                for u in X:
                    tot["X"] += 1
                    if t1 < 0:
                        tot["t_neg"] += 1
                        continue
                    v = apply_flips(u, (t1, t2))
                    if not safe2(v, a, b):
                        tot["psi_unsafe"] += 1
                        if len(fails) < 10:
                            fails.append((a, b, n, u, t1, t2))
                        continue
                    tot["psi_safe"] += 1
                    if cval(v, j - 1, g) == 1 and cval(v, j, g) == 1:
                        tot["lands_11"] += 1
                    else:
                        tot["lands_bad"] += 1
    print(f"    {dict(tot)}")
    for f in fails:
        print(f"    unsafe example a={f[0]} b={f[1]} n={f[2]} u={f[3]} "
              f"t1={f[4]} t2={f[5]}")

    print("[Q] coverage of X by safe single flips: flip_j (needs c_{j-a}=0), "
          "flip_{j-g}, flip_{j-1-g}")
    cov = Counter()
    for a in range(2, 7):
        for b in range(a + 1, 10):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a, 15):
                j = n - a
                Aprev = words(n - 1, a, b)
                X = [u for u in Aprev
                     if cval(u, j - 1, g) == 0 and cval(u, j, g) == 0]
                for u in X:
                    cov["X"] += 1
                    any_ok = False
                    for t, tgt in ((j, (0, 1)), (j - g, (0, 1)),
                                   (j - 1 - g, (1, 0))):
                        if t < 0:
                            continue
                        v = apply_flips(u, (t,))
                        if v is None or not safe2(v, a, b):
                            continue
                        # must move to c_j=1 or (1,1)
                        if cval(v, j, g) == 1 or \
                           (cval(v, j - 1, g) == 1 and cval(v, j, g) == 1):
                            any_ok = True
                    if any_ok:
                        cov["has_single"] += 1
                    else:
                        cov["no_single"] += 1
    print(f"    {dict(cov)}")


if __name__ == "__main__":
    main()
