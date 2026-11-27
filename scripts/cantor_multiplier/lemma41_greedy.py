# Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
# Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
# Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
"""Test greedy injection rules: process E-part elements in a canonical order,
each takes the first admissible target (size<=2 flips first, then size 3)
not yet used. Orders:
  lex        : word lexicographic
  contested  : contested first (lex), then others (lex)
  fewopt     : ascending number of options (ties: lex)
Report which orders succeed for all (a,b,n), and failure counts.
"""
from itertools import product, combinations
from math import gcd
from collections import Counter, defaultdict


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


def build_candidates(u, L, j, g, a, b, maxsz=3):
    """Return ordered candidate images: size<=2 lex order, then size 3."""
    out = []
    for p in range(L):
        v = flipset(u, (p,))
        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
            out.append(v)
    for p, q in combinations(range(L), 2):
        v = flipset(u, (p, q))
        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
            out.append(v)
    if maxsz >= 3:
        for S in combinations(range(L), 3):
            v = flipset(u, S)
            if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                out.append(v)
    return out


def main():
    tot = Counter()
    fails = defaultdict(list)
    for a in range(2, 8):
        for b in range(a + 1, 11):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a + 1, 17):
                j = n - a
                t = j - g
                r = n - g
                L = n - 1
                Aprev = words(n - 1, a, b)
                # first-fit (branch assignment as in lemma41_full)
                img_of, br_of = {}, {}
                for u in Aprev:
                    if cval(u, j - 1, g) or cval(u, j, g):
                        continue
                    if cval(u, j - a, g) == 0:
                        img_of[u] = flipset(u, (j,))
                        br_of[u] = "b1"
                        continue
                    ph = None
                    for name, ts in (("b2", (t,)), ("b3", (t, r)),
                                     ("b4", (t, r - b))):
                        v = flipset(u, ts)
                        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                            ph = v
                            break
                    img_of[u] = ph
                    br_of[u] = name if ph else "none"
                ffimgs = set(v for v in img_of.values() if v is not None)
                Epart = sorted([u for u in img_of
                                if br_of[u] in ("b2", "b3", "b4")])
                if not Epart:
                    tot["noE"] += 1
                    continue
                cands = {u: build_candidates(u, L, j, g, a, b) for u in Epart}
                b1imgs = set(v for u, v in img_of.items() if br_of[u] == "b1")
                for u in Epart:
                    cands[u] = [v for v in cands[u] if v not in b1imgs]
                contested = set()
                grp = defaultdict(list)
                for u in Epart:
                    if img_of[u] is not None:
                        grp[img_of[u]].append(u)
                for im, us in grp.items():
                    if len(us) > 1:
                        contested.update(us)
                orders = {
                    "lex": lambda: Epart,
                    "contested": lambda: sorted(
                        Epart, key=lambda u: (0 if u in contested else 1, u)),
                    "fewopt": lambda: sorted(
                        Epart, key=lambda u: (len(cands[u]), u)),
                }
                for name, key in orders.items():
                    used = set()
                    okall = True
                    for u in key():
                        got = None
                        for v in cands[u]:
                            if v not in used:
                                got = v
                                break
                        if got is None:
                            okall = False
                            break
                        used.add(got)
                    if okall:
                        tot[name + "_ok"] += 1
                    else:
                        tot[name + "_fail"] += 1
                        if len(fails[name]) < 8:
                            fails[name].append((a, b, n))
    print(dict(tot))
    for k, v in fails.items():
        print(k, "fails:", v)


if __name__ == "__main__":
    main()
