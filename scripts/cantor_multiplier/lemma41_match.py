# Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
# Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
# Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
"""Lemma 4.1 collision diagnosis: for each (a,b,n), build the bipartite graph
E-part of G  ->  admissible targets (safe, c_j=1) via flips of size <= 2,
and test whether a perfect matching exists (i.e. can all contested elements
be assigned distinct targets). Also stats on alternatives per element.
"""
from itertools import product, combinations
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
    n = len(v)
    for i in range(n):
        zi = v[i]
        za = v[i - a] if i - a >= 0 else 0
        zb = v[i - b] if i - b >= 0 else 0
        if not (0 <= zi - za + zb <= 1):
            return False
    return True


def kuhn_match(left, cand, nright):
    """left: list of node ids; cand[u] = list of right nodes; returns match dict right->u"""
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
    nomatch = []
    alt_stats = Counter()
    for a in range(2, 8):
        for b in range(a + 1, 11):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a + 1, 17):
                j = n - a
                t = j - g
                Aprev = words(n - 1, a, b)
                L = len(Aprev[0]) if Aprev else n - 1
                # first-fit assignment exactly as lemma41_full
                img_of = {}
                for u in Aprev:
                    if cval(u, j - 1, g) or cval(u, j, g):
                        continue
                    if cval(u, j - a, g) == 0:
                        img_of[u] = flipset(u, (j,))
                        continue
                    ph = None
                    for ts in ((t,), (t, n - g), (t, n - g - b)):
                        v = flipset(u, ts)
                        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                            ph = v
                            break
                    img_of[u] = ph
                Epart = [u for u in img_of if cval(u, j - a, g) == 1]
                # contested: image shared with another element
                from collections import defaultdict
                grp = defaultdict(list)
                for u, im in img_of.items():
                    if im is not None:
                        grp[im].append(u)
                contested = set()
                for im, us in grp.items():
                    if len(us) > 1:
                        for u in us:
                            contested.add(u)
                # candidates: any flip size <=2 -> safe image with c_j=1
                singles = list(range(L))
                pairs = list(combinations(singles, 2))
                cand = {}
                for u in Epart:
                    opts = []
                    for S in [(p,) for p in singles] + pairs:
                        v = flipset(u, S)
                        if v is None or not safe(v, a, b):
                            continue
                        if cval(v, j, g) != 1:
                            continue
                        opts.append(v)
                    cand[u] = opts
                    if u in contested:
                        others = [v for v in opts if v != img_of[u]]
                        alt_stats["contested"] += 1
                        if others:
                            alt_stats["has_other_1or2flip"] += 1
                        single_others = [
                            v for p in singles
                            if (v := flipset(u, (p,))) is not None
                            and safe(v, a, b) and cval(v, j, g) == 1
                            and v != img_of[u]]
                        if single_others:
                            alt_stats["has_other_single"] += 1
                # perfect matching on Epart (exclude b1 images from targets)
                b1imgs = set(v for u, v in img_of.items()
                             if cval(u, j - a, g) == 0)
                cand2 = {u: [v for v in cand[u] if v not in b1imgs]
                         for u in Epart}
                if any(not cand2[u] for u in Epart):
                    tot["elem_no_candidate"] += 1
                    nomatch.append((a, b, n, "no-cand-elem"))
                    continue
                m = kuhn_match(Epart, cand2, None)
                if m is None:
                    tot["matching_fail"] += 1
                    nomatch.append((a, b, n, "matching"))
                else:
                    tot["matching_ok"] += 1
                # duplicate count under first-fit
                if any(len(us) > 1 for us in grp.values()):
                    tot["ff_dup_groups"] += sum(
                        1 for us in grp.values() if len(us) > 1)
    print(dict(tot))
    print("alt stats:", dict(alt_stats))
    for x in nomatch[:20]:
        print("  nomatch:", x)


if __name__ == "__main__":
    main()
