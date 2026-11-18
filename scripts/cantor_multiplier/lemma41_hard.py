"""Lemma 4.1: the 206 residual cases with NO safe single flip.

For each u in X={(c_{j-1},c_j)=(0,0)} where both flip_j and flip_{j-g} are
unsafe (or land outside Y), brute-force all safe 2-flips and 3-flips that
land in Y={c_j=1}, looking for a uniform rule.
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


def apply_flips(w, ts):
    v = list(w)
    for t in ts:
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


def broken(w, i, a, b):
    zi = w[i]
    za = w[i - a] if i - a >= 0 else 0
    zb = w[i - b] if i - b >= 0 else 0
    return not (0 <= zi - za + zb <= 1)


def main():
    hard = []
    for a in range(2, 7):
        for b in range(a + 1, 10):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a, 15):
                j = n - a
                for u in words(n - 1, a, b):
                    if cval(u, j - 1, g) != 0 or cval(u, j, g) != 0:
                        continue
                    ok1 = ok2 = False
                    for t in (j, j - g):
                        if t < 0:
                            continue
                        v = apply_flips(u, (t,))
                        if safe(v, a, b) and cval(v, j, g) == 1:
                            if t == j:
                                ok1 = True
                            else:
                                ok2 = True
                    if not ok1 and not ok2:
                        hard.append((a, b, n, g, j, u))
    print(f"hard cases: {len(hard)}")
    bypair = Counter((h[0], h[1]) for h in hard)
    print(f"by pair: {dict(bypair)}")
    print("first 12:")
    for h in hard[:12]:
        print(f"    a={h[0]} b={h[1]} n={h[2]} j={h[4]} u={h[5]}")

    # which constraints break under flip_{j-g}?
    brk = Counter()
    for (a, b, n, g, j, u) in hard:
        t = j - g
        if t >= 0:
            v = apply_flips(u, (t,))
            for i in range(n - 1):
                if broken(v, i, a, b):
                    brk[i - t] += 1  # offset of broken constraint from t
    print(f"broken-constraint offsets under flip_{{j-g}}: {dict(brk)}")

    # brute force: safe 2-flips landing in Y
    found = Counter()
    rule = Counter()
    for (a, b, n, g, j, u) in hard:
        got = None
        for ts in combinations(range(n - 1), 2):
            v = apply_flips(u, ts)
            if safe(v, a, b) and cval(v, j, g) == 1:
                got = ts
                break
        if got is None:
            for ts in combinations(range(n - 1), 3):
                v = apply_flips(u, ts)
                if safe(v, a, b) and cval(v, j, g) == 1:
                    got = ts
                    break
        if got is None:
            found["none"] += 1
        else:
            found[f"size{len(got)}"] += 1
            # does the flip set contain j or j-g (needed to toggle c_j)?
            has_cj = (j in got) or (j - g in got)
            rule[f"contains_j_or_jg={has_cj}"] += 1
            rule[f"set={tuple(sorted(got))}"] += 1
    print(f"brute-force 2/3-flip solutions: {dict(found)}")
    print(f"c_j-toggle membership: { {k: v for k, v in rule.items() if 'contains' in k} }")
    top = sorted(((k, v) for k, v in rule.items() if k.startswith('set=')),
                 key=lambda x: -x[1])[:10]
    print(f"top flip sets: {top}")


if __name__ == "__main__":
    main()
