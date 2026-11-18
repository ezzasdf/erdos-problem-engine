"""Lemma 4.1 combinatorial verification.

Chain SFT: z in {0,1}^n (z_j = 0 for j<0), constraint
    z_i - z_{i-a} + z_{i-b} in {0,1}  for all i<n.
Equivalent: lag-a flips subset of lag-b flips.
Goal: Fibonacci-type bound N(n+1) <= N(n) + N(n-1) (eventually),
giving growth <= phi.
"""
from itertools import product
from math import gcd


def direct_ok(w, a, b):
    n = len(w)
    for i in range(n):
        zi = w[i]
        za = w[i - a] if i - a >= 0 else 0
        zb = w[i - b] if i - b >= 0 else 0
        if not (0 <= zi - za + zb <= 1):
            return False
    return True


def flips_subset_ok(w, a, b):
    """A = lag-a flips, B = lag-b flips, require A subset B (within [0,n))."""
    n = len(w)
    for i in range(n):
        za = w[i - a] if i - a >= 0 else 0
        zb = w[i - b] if i - b >= 0 else 0
        if w[i] != za and w[i] == zb:
            return False
    return True


def enumerate_words(n, a, b):
    return [w for w in product((0, 1), repeat=n) if direct_ok(w, a, b)]


def cval(w, j, g):
    """c_j = z_j xor z_{j-g}, with z_{<0}=0."""
    zj = w[j] if 0 <= j < len(w) else 0
    zg = w[j - g] if j - g >= 0 else 0
    return zj ^ zg


def main():
    # 1. characterization check
    chars = 0
    for a in range(1, 8):
        for b in range(a + 1, 9):
            if gcd(a, b) != 1:
                continue
            for n in range(0, 7):
                for w in product((0, 1), repeat=n):
                    assert direct_ok(w, a, b) == flips_subset_ok(w, a, b), (a, b, w)
                    chars += 1
    print(f"[1] A-subset-B characterization verified on {chars} words OK")

    # 2. Fibonacci recurrence N(n) <= N(n-1)+N(n-2): find threshold n0
    print("[2] thresholds for N(n) <= N(n-1)+N(n-2):")
    worst_n0 = 0
    for a in range(1, 8):
        for b in range(a + 1, 10):
            if gcd(a, b) != 1:
                continue
            N = {}
            for n in range(0, 18):
                N[n] = len(enumerate_words(n, a, b))
            n0 = None
            for n in range(2, 18):
                if N[n] > N[n - 1] + N[n - 2]:
                    n0 = n + 1  # first n where it must hold after a failure at n
            # find smallest m such that holds for all n in [m,17]
            m = 2
            for n in range(2, 18):
                if N[n] > N[n - 1] + N[n - 2]:
                    m = n + 1
            holds = all(N[n] <= N[n - 1] + N[n - 2] for n in range(m, 18))
            worst_n0 = max(worst_n0, m)
            print(f"    (a,b)=({a},{b}) N(0..6)={[N[i] for i in range(7)]}"
                  f" recurrence holds for n>={m} (checked to 17): {holds}")
    print(f"    worst threshold: n >= {worst_n0}")

    # 3. drop-last injection for a=1: fiber over u has <=1 free word
    print("[3] a=1 drop-last fiber check:")
    ok = True
    for b in range(2, 9):
        if gcd(1, b) != 1:
            continue
        a = 1
        for n in range(1, 16):
            An = enumerate_words(n, a, b)
            for u in An:  # u = word of length n, check free fibers at pos n
                pass
            # fibers: group A_n words by prefix of length n-1, count those with pos n free
            from collections import defaultdict
            fib = defaultdict(int)
            for w in An:
                # pos n free in w: z_{n-a} == z_{n-b}
                za = w[n - a] if n - a >= 0 else 0
                zb = w[n - b] if n - b >= 0 else 0
                if za == zb:
                    fib[w[:-1]] += 1
            for u, cnt in fib.items():
                if cnt > 1:
                    ok = False
                    print(f"    FAIL a=1 b={b} n={n} u={u} fiber={cnt}")
    print(f"    drop-last injective on free set for a=1: {ok}")

    # 4. for a>=2: B(n) <= N(n-1)  and the refined pair count condition
    print("[4] a>=2: B(n)<=N(n-1) and N_00 <= N_01+N_11:")
    okB = True
    okPair = True
    for a in range(2, 8):
        for b in range(a + 1, 10):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for n in range(1, 16):
                An = enumerate_words(n, a, b)
                # B(n) = # w in A_n with pos n free
                B = 0
                for w in An:
                    za = w[n - a] if n - a >= 0 else 0
                    zb = w[n - b] if n - b >= 0 else 0
                    if za == zb:
                        B += 1
                Nprev = len(enumerate_words(n - 1, a, b))
                if B > Nprev:
                    okB = False
                    print(f"    FAIL B a={a} b={b} n={n} B={B} N(n-1)={Nprev}")
                # pair condition: u in A_{n-1}, j = n-a
                j = n - a
                if j >= 1:
                    N00 = N01 = N10 = N11 = 0
                    for u in enumerate_words(n - 1, a, b):
                        cj1 = cval(u, j - 1, g)
                        cj = cval(u, j, g)
                        if cj1 == 0 and cj == 0:
                            N00 += 1
                        elif cj1 == 0 and cj == 1:
                            N01 += 1
                        elif cj1 == 1 and cj == 0:
                            N10 += 1
                        else:
                            N11 += 1
                    if N00 > N01 + N11:
                        okPair = False
                        print(f"    FAIL pair a={a} b={b} n={n} "
                              f"N00={N00} N01={N01} N10={N10} N11={N11}")
    print(f"    B(n) <= N(n-1): {okB}")
    print(f"    N_00 <= N_01+N_11: {okPair}")


if __name__ == "__main__":
    main()
