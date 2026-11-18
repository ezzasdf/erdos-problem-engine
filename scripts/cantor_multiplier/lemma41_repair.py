"""Lemma 4.1: find a uniform repair rule for the hard cases.

Hard u in G=X=(c_{j-1},c_j)=(0,0) with c_{j-a}=1 (flip_j unsafe) and
flip_{j-g} unsafe. Any landing map into Z={c_j=1} must flip an odd number
of bits from {j, j-g}. Test candidate r for the 2-flip {j-g, r} or {j, r}:
report which r work per (a,b,n), then look for a uniform formula.
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
    # collect hard cases
    hard = []
    for a in range(2, 7):
        for b in range(a + 1, 10):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a, 15):
                j = n - a
                for u in words(n - 1, a, b):
                    if cval(u, j - 1, g) or cval(u, j, g):
                        continue
                    if cval(u, j - a, g) == 0:
                        continue  # flip_j handles it
                    ok = False
                    for t in (j, j - g):
                        if t < 0:
                            continue
                        v = flipset(u, (t,))
                        if v and safe(v, a, b) and cval(v, j, g) == 1:
                            ok = True
                    if not ok:
                        hard.append((a, b, n, g, j, u))
    print(f"hard: {len(hard)}")

    # for each hard u: which single-bit repairs r make {t, r} safe (t=j-g or t=j)
    cand_counter = Counter()
    per_group = defaultdict(set)
    for (a, b, n, g, j, u) in hard:
        good = set()
        for t in (j - g, j):
            if t < 0:
                continue
            for r in range(n - 1):
                if r == t:
                    continue
                v = flipset(u, (t, r))
                if v and safe(v, a, b) and cval(v, j, g) == 1:
                    good.add((t - j, r - j))  # offsets from j
        per_group[(a, b, n)].add(frozenset(good))
        for gg in good:
            cand_counter[gg] += 1
    print("candidate (t-j, r-j) offsets by frequency:")
    for k, v in cand_counter.most_common(20):
        print(f"    t-j={k[0]} r-j={k[1]} : {v}")

    # does a formula r = i* = n-g  (r-j = n-g-j = a-g) or r = i*-b work for all?
    print("\nformula checks:")
    for name, rf in (
        ("r=i*=n-g", lambda a, b, n, j: n - (b - a)),
        ("r=i*-b=n-g-b", lambda a, b, n, j: n - (b - a) - b),
        ("r=j-a", lambda a, b, n, j: j - a),
        ("r=j-b", lambda a, b, n, j: j - b),
        ("r=n-1", lambda a, b, n, j: n - 2),
        ("r=j+1", lambda a, b, n, j: j + 1),
    ):
        okc = failc = 0
        for (a, b, n, g, j, u) in hard:
            r = rf(a, b, n, j)
            worked = False
            for t in (j - g, j):
                if t < 0 or r == t or not (0 <= r < n - 1):
                    continue
                v = flipset(u, (t, r))
                if v and safe(v, a, b) and cval(v, j, g) == 1:
                    worked = True
            if worked:
                okc += 1
            else:
                failc += 1
        print(f"    {name}: works {okc}, fails {failc}")

    # per-group intersection: is there one (t,r) offset working for every u in group?
    single = 0
    multi = 0
    for key, sets in per_group.items():
        inter = set.intersection(*[set(s) for s in sets]) if sets else set()
        if inter:
            single += 1
        else:
            multi += 1
    print(f"\ngroups with one common (t,r) for all hard u: {single}, "
          f"without: {multi}")


if __name__ == "__main__":
    main()
