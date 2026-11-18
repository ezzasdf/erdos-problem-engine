"""Lemma 4.1 crux: balance inequalities and flip injections.

Setup (a>=2, g=b-a, j=n-a, c_m = z_m xor z_{m-g}, z_{<0}=0):
  S  = {u in A_{n-1}: c_j = 0}          (= position n free)
  T  = {u: c_{j-1} = 0}                  (= position n-1 free)
  B(n) = #{u: c_j=0} + #{u: c_{j-1}=0, c_j=0} ... target B(n) <= N(n-1)
  equivalent: N_00 <= N_01 + N_11   (known true)
Candidate stronger: N_00 <= N_01 (only pair within {c_{j-1}=0}).
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


def enumerate_words(n, a, b):
    return [w for w in product((0, 1), repeat=n) if direct_ok(w, a, b)]


def cval(w, m, g):
    zj = w[m] if 0 <= m < len(w) else 0
    zg = w[m - g] if m - g >= 0 else 0
    return zj ^ zg


def free_at(w, i, a, b):
    za = w[i - a] if i - a >= 0 else 0
    zb = w[i - b] if i - b >= 0 else 0
    return za == zb


def flip(w, t):
    v = list(w)
    v[t] ^= 1
    return tuple(v)


def constraint_ok(w, i, a, b):
    zi = w[i] if i < len(w) else 0
    za = w[i - a] if i - a >= 0 else 0
    zb = w[i - b] if i - b >= 0 else 0
    return 0 <= zi - za + zb <= 1


def flip_safe(u, t, a, b):
    """u in A_{len}; flip bit t; all constraints of u still valid?"""
    v = flip(u, t)
    n = len(u)
    return all(constraint_ok(v, i, a, b) for i in range(n))


def main():
    print("[I1] N_00 <= N_01  (within {c_{j-1}=0}: c_j <= half zeros)")
    print("[I2] N_00 <= N_11")
    bad1 = bad2 = 0
    for a in range(2, 8):
        for b in range(a + 1, 11):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a, 17):
                j = n - a
                if j < 1:
                    continue
                cnt = Counter()
                for u in enumerate_words(n - 1, a, b):
                    cj1 = cval(u, j - 1, g)
                    cj = cval(u, j, g)
                    cnt[(cj1, cj)] += 1
                N00 = cnt[(0, 0)]
                N01 = cnt[(0, 1)]
                N11 = cnt[(1, 1)]
                if N00 > N01:
                    bad1 += 1
                    if bad1 <= 8:
                        print(f"    I1 FAIL (a,b)=({a},{b}) n={n} j={j} "
                              f"N00={N00} N01={N01} N11={N11}")
                if N00 > N11:
                    bad2 += 1
                    if bad2 <= 8:
                        print(f"    I2 FAIL (a,b)=({a},{b}) n={n} j={j} "
                              f"N00={N00} N01={N01} N11={N11}")
    print(f"    I1 fails: {bad1}, I2 fails: {bad2}")

    print("[J] flip_j pairing sanity: flip_j maps D={c_{j-a}=0} involution, "
          "toggles c_j, preserves c_{j-1}")
    okj = True
    for a in range(2, 7):
        for b in range(a + 1, 10):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a + 1, 15):
                j = n - a
                for u in enumerate_words(n - 1, a, b):
                    if cval(u, j - a, g) == 0:
                        v = flip(u, j)
                        if not flip_safe(u, j, a, b):
                            okj = False
                            print(f"    flip_j unsafe a={a} b={b} n={n} u={u}")
                        if flip_safe(u, j, a, b):
                            if cval(v, j, g) != 1 - cval(u, j, g) or \
                               cval(v, j - 1, g) != cval(u, j - 1, g):
                                okj = False
                                print(f"    flip_j c-effect wrong a={a} b={b} n={n}")
    print(f"    flip_j safe/toggles on D: {okj}")

    print("[K] residual: within E={c_{j-a}=1} and {c_{j-1}=0}, c_j=0, "
          "does flip at t=j-g land in Y and stay safe?")
    stats = Counter()
    for a in range(2, 7):
        for b in range(a + 1, 10):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a, 15):
                j = n - a
                t = j - g
                for u in enumerate_words(n - 1, a, b):
                    if cval(u, j - a, g) == 1 and cval(u, j - 1, g) == 0 \
                       and cval(u, j, g) == 0:
                        stats["residual"] += 1
                        if t < 0:
                            stats["t_neg"] += 1
                            continue
                        if not flip_safe(u, t, a, b):
                            stats["unsafe"] += 1
                            continue
                        v = flip(u, t)
                        if cval(v, j, g) == 1:
                            stats["lands_Y"] += 1
                        else:
                            stats["not_Y"] += 1
                        if cval(v, j - a, g) == 1:
                            stats["stays_E"] += 1
    print(f"    {dict(stats)}")

    print("[L] conditional balance: within {c_{j-1}=0, c_{j-a}=1} "
          "(residual), is c_j <= half zeros?")
    badL = 0
    for a in range(2, 7):
        for b in range(a + 1, 10):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(a, 15):
                j = n - a
                z0 = z1 = 0
                for u in enumerate_words(n - 1, a, b):
                    if cval(u, j - a, g) == 1 and cval(u, j - 1, g) == 0:
                        if cval(u, j, g) == 0:
                            z0 += 1
                        else:
                            z1 += 1
                if z0 > z1:
                    badL += 1
                    if badL <= 8:
                        print(f"    L FAIL a={a} b={b} n={n} zeros={z0} ones={z1}")
    print(f"    L fails: {badL}")


if __name__ == "__main__":
    main()
