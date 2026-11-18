"""Pair-level matching: each conflict pair {x,y} must get ONE fresh target
(outside all first-fit images, size<=3 flips, lands in Z) for either x or y;
keeper takes contested w. Bipartite: pairs -> union of fresh sets.
Check perfect pair-matching for all (a,b,n).
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


def fresh_cands(u, L, j, g, a, b, ffimgs, maxsz=4):
    out = []
    for sz in range(1, maxsz + 1):
        for S in combinations(range(L), sz):
            v = flipset(u, S)
            if v is None or not safe(v, a, b) or cval(v, j, g) != 1:
                continue
            if v in ffimgs:
                continue
            out.append(v)
        if out:
            return out
    return out


def kuhn(left, cand):
    match = {}

    def try_k(u, seen):
        for r in cand[u]:
            if r in seen:
                continue
            seen.add(r)
            if r not in match or try_k(match[r], seen):
                match[r] = u
                return True
        return False

    for u in left:
        if not try_k(u, set()):
            return None
    return match


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
                img_of = {}
                for u in Aprev:
                    if cval(u, j - 1, g) or cval(u, j, g):
                        continue
                    if cval(u, j - a, g) == 0:
                        img_of[u] = flipset(u, (j,))
                        continue
                    ph = None
                    for ts in ((t,), (t, r), (t, r - b)):
                        v = flipset(u, ts)
                        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                            ph = v
                            break
                    img_of[u] = ph
                ffimgs = set(v for v in img_of.values() if v is not None)
                grp = defaultdict(list)
                for u, im in img_of.items():
                    if im is not None:
                        grp[im].append(u)
                pairs = [tuple(sorted(us)) for im, us in grp.items()
                         if len(us) == 2]
                if not pairs:
                    tot["ok"] += 1
                    continue
                cand = {}
                for i, (x, y) in enumerate(pairs):
                    fx = fresh_cands(x, L, j, g, a, b, ffimgs)
                    fy = fresh_cands(y, L, j, g, a, b, ffimgs)
                    cand[i] = sorted(set(fx) | set(fy))
                    if not cand[i]:
                        tot["pair_no_fresh"] += 1
                if any(not cand[i] for i in range(len(pairs))):
                    tot["fail_nocand"] += 1
                    fails.append((a, b, n, "nocand"))
                    continue
                m = kuhn(list(range(len(pairs))), cand)
                if m is None:
                    tot["fail_match"] += 1
                    fails.append((a, b, n, "match"))
                else:
                    tot["ok"] += 1
    print(dict(tot))
    for f in fails[:20]:
        print("  fail:", f)


if __name__ == "__main__":
    main()
