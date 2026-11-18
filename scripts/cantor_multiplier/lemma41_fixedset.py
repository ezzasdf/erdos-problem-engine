"""Is there a FIXED flip set S (independent of u) with
   forall u in G: u^S admissible and c_j(u^S)=1 ?
Sizes up to 4. Also same with G split by c_{j-a} (D/E): fixed S on each part.
S may depend on (a,b,n). Report per-config existence + size distribution.
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
    for i in range(len(v)):
        zi = v[i]
        za = v[i - a] if i - a >= 0 else 0
        zb = v[i - b] if i - b >= 0 else 0
        if not (0 <= zi - za + zb <= 1):
            return False
    return True


def main():
    tot = Counter()
    fail_cfgs = []
    examples = {}
    for a in range(2, 7):
        for b in range(a + 1, 10):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a + 1, 15):
                j = n - a
                Aprev = words(n - 1, a, b)
                L = n - 1
                G = [u for u in Aprev
                     if not cval(u, j - 1, g) and not cval(u, j, g)]
                if not G:
                    continue
                # exhaustive search over S, |S| <= 4
                found = None
                for sz in range(1, 5):
                    for S in combinations(range(L), sz):
                        ok = True
                        for u in G:
                            v = flipset(u, S)
                            if v is None or not safe(v, a, b) or \
                               cval(v, j, g) != 1:
                                ok = False
                                break
                        if ok:
                            found = S
                            break
                    if found is not None:
                        tot[f"size{sz}"] += 1
                        break
                if found is None:
                    tot["none_le4"] += 1
                    if len(fail_cfgs) < 15:
                        fail_cfgs.append((a, b, n, len(G), L))
                else:
                    key = (a, b, n - a, g)
                    examples.setdefault(key, found)
    print(dict(tot))
    print("fail cfgs:", fail_cfgs)
    print("examples (a,b,n-a,g): S")
    for k in sorted(examples):
        print("  ", k, examples[k])


if __name__ == "__main__":
    main()
