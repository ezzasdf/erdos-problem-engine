# Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
# Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
# Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
"""Canonical conflict resolution test.
For each (a,b,n): first-fit assignment; find dup groups (all size 2).
Resolve each pair canonically:
  keepers: the member whose first-fit image is NOT claimed by a partner
  (i.e. uncontested images) stay; for each contested pair {x,y}:
    option A: y keeps w, x moves to lex-first candidate outside ffimgs
              (candidates: size<=2 then size<=3, lex order of flip set)
    option B: x keeps w, y moves likewise
  Rule: try A first (mover=x = the member with smaller word), else B.
  Movers must also avoid targets chosen by previous pairs.
Check: every pair resolvable + all final images distinct + in Z.
Also record which side had to move (stats) and whether size 3 was needed.
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


def cands_for(u, L, j, g, a, b, maxsz=3):
    out = []
    for sz in (1, 2, 3):
        if sz > maxsz:
            break
        for S in combinations(range(L), sz):
            v = flipset(u, S)
            if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                out.append(v)
        if out:
            break  # prefer smallest size first
    return out


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
                L = n - 1
                Aprev = words(n - 1, a, b)
                img_of, br_of = {}, {}
                for u in Aprev:
                    if cval(u, j - 1, g) or cval(u, j, g):
                        continue
                    if cval(u, j - a, g) == 0:
                        img_of[u] = flipset(u, (j,))
                        br_of[u] = "b1"
                        continue
                    ph, br = None, None
                    for name, ts in (("b2", (t,)), ("b3", (t, r)),
                                     ("b4", (t, r - b))):
                        v = flipset(u, ts)
                        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                            ph, br = v, name
                            break
                    img_of[u], br_of[u] = ph, (br or "none")
                ffimgs = set(v for v in img_of.values() if v is not None)
                grp = defaultdict(list)
                for u, im in img_of.items():
                    if im is not None:
                        grp[im].append(u)
                pairs = [sorted(us) for im, us in grp.items() if len(us) == 2]
                if any(len(us) > 2 for us in grp.values()):
                    tot["triple+"] += 1
                final = {}
                taken = set()
                # uncontested keepers first
                for im, us in grp.items():
                    if len(us) == 1:
                        final[us[0]] = im
                        taken.add(im)
                ok = True
                for pair in sorted(pairs):
                    x, y = pair  # x < y lexicographically
                    w = img_of[x]
                    resolved = False
                    for mover, keeper in ((x, y), (y, x)):
                        for v in cands_for(mover, L, j, g, a, b):
                            if v in ffimgs:
                                continue  # fresh targets only
                            if v in taken:
                                continue
                            # keeper must still be able to keep w
                            final[mover] = v
                            final[keeper] = w
                            taken.add(v)
                            taken.add(w)
                            tot["mover_is_x" if mover is x else "mover_is_y"] += 1
                            resolved = True
                            break
                        if resolved:
                            break
                    if not resolved:
                        ok = False
                        break
                if not ok:
                    tot["fail"] += 1
                    if len(fails) < 10:
                        fails.append((a, b, n, len(pairs)))
                    continue
                tot["ok"] += 1
                # global distinctness + validity
                imgs = list(final.values())
                if len(set(imgs)) != len(imgs):
                    tot["dup_after"] += 1
                    fails.append(("dup", a, b, n))
                for v in imgs:
                    if not safe(v, a, b) or cval(v, j, g) != 1:
                        tot["bad_after"] += 1
    print(dict(tot))
    for f in fails:
        print("  fail:", f)


if __name__ == "__main__":
    main()
