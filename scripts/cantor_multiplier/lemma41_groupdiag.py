"""Lemma 4.1: characterize duplicate-image groups and per-member alternatives.

Questions:
 1. group sizes (are all dup groups pairs {u, theta(u)} with theta=flip{n-g}?)
 2. for each dup group: does the b3-side member have an alternative target
    outside ALL first-fit images? and the b2-side?
 3. what are the 23 contested elements with no other 1/2-flip candidate?
 4. is psi2 (=flip{t, n-g-b}) available for b3-side members?
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


def main():
    tot = Counter()
    noalt = []
    groupsizes = Counter()
    pair_theta = Counter()
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
                L = n - 1
                # first-fit
                img_of = {}
                br_of = {}
                for u in Aprev:
                    if cval(u, j - 1, g) or cval(u, j, g):
                        continue
                    if cval(u, j - a, g) == 0:
                        img_of[u] = flipset(u, (j,))
                        br_of[u] = "b1"
                        continue
                    done = False
                    for name, ts in (("b2", (t,)), ("b3", (t, r)),
                                     ("b4", (t, r - b))):
                        v = flipset(u, ts)
                        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                            img_of[u] = v
                            br_of[u] = name
                            done = True
                            break
                    if not done:
                        img_of[u] = None
                        br_of[u] = "none"
                ffimgs = set(v for v in img_of.values() if v is not None)
                # all candidates for each E element
                cands = {}
                for u, br in br_of.items():
                    if br in ("b1", "none"):
                        continue
                    opts = []
                    for p in range(L):
                        v = flipset(u, (p,))
                        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                            opts.append(v)
                    for p, q in combinations(range(L), 2):
                        v = flipset(u, (p, q))
                        if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                            opts.append(v)
                    cands[u] = opts
                # dup groups
                grp = defaultdict(list)
                for u, im in img_of.items():
                    if im is not None:
                        grp[im].append(u)
                for im, us in grp.items():
                    if len(us) < 2:
                        continue
                    groupsizes[len(us)] += 1
                    # is every member image = first-fit of others? check theta relation
                    thetas = all(
                        any(set(x) ^ set(y) == {r} for y in us if y is not x)
                        or len(us) == 1
                        for x in us)
                    pair_theta[len(us) == 2 and thetas] += 1
                    # alternatives outside ffimgs
                    fresh = {}
                    for u in us:
                        others = [v for v in cands.get(u, [])
                                  if v not in ffimgs]
                        fresh[u] = others
                    if not any(fresh[u] for u in us):
                        tot["group_no_fresh_any"] += 1
                        if len(noalt) < 12:
                            noalt.append((a, b, n, br_of[us[0]],
                                          br_of[us[1]] if len(us) > 1 else None))
                    else:
                        tot["group_resolvable"] += 1
                    if len(us) == 2:
                        u1, u2 = us
                        if br_of[u1] == "b3" and br_of[u2] == "b2":
                            tot["pair_b3_b2"] += 1
                            # psi2 availability for b3 side
                            v = flipset(u1, (t, r - b))
                            if v is not None and safe(v, a, b) and cval(v, j, g) == 1:
                                tot["b3side_psi2_ok"] += 1
                            if fresh[u1]:
                                tot["b3side_has_fresh"] += 1
                            if fresh[u2]:
                                tot["b2side_has_fresh"] += 1
                        elif br_of[u1] == "b2" and br_of[u2] == "b3":
                            tot["pair_b2_b3"] += 1
                        else:
                            tot["pair_other:" + br_of[u1] + "," + br_of[u2]] += 1
                # contested with no alternatives at all
                for u, opts in cands.items():
                    if img_of[u] is not None and len(grp[img_of[u]]) > 1:
                        if all(v == img_of[u] for v in opts):
                            tot["contested_no_alt_at_all"] += 1
                            if len(noalt) < 12:
                                noalt.append(("noalt", a, b, n, br_of[u]))
    print(dict(tot))
    print("group sizes:", dict(groupsizes))
    print("theta pairs:", dict(pair_theta))
    for x in noalt:
        print("  ", x)


if __name__ == "__main__":
    main()
