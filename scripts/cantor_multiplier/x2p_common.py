#!/usr/bin/env python3
"""Shared helpers for the x2P study: critical-gap class transitions under * 2^P."""
import os, sys, time
from functools import lru_cache
from decimal import Decimal, getcontext

sys.setrecursionlimit(100000)
getcontext().prec = 60

P = 162 * 59049           # 9565938 = 2*3^14
LOG3_2 = Decimal(2).ln() / Decimal(3).ln()
CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "cache")
os.makedirs(CACHE, exist_ok=True)


def Kstar(r):
    return int(Decimal(r) * LOG3_2)


@lru_cache(maxsize=None)
def pow3(n):
    return 3 ** n


def to_base3_bytes(n, m):
    """Little-endian base-3 digits of n padded/truncated to m digits."""
    out = bytearray(m)

    def rec(off, m_, val):
        if m_ <= 512:
            v = val
            for k in range(m_):
                out[off + k] = v % 3
                v //= 3
            return
        h = m_ // 2
        p = pow3(h)
        rec(off, h, val % p)
        rec(off + h, m_ - h, val // p)

    rec(0, m, n)
    return out


def gword(r, tag=None, verbose=True):
    """Digits of G(r) = 2^r - 3^{K*(r)}, length K*+1. Cached to disk."""
    K = Kstar(r)
    m = K + 1
    path = os.path.join(CACHE, f"G_{tag or r}.b3")
    if os.path.exists(path):
        data = open(path, "rb").read()
        if len(data) == m:
            return data
    t0 = time.time()
    w = to_base3_bytes(pow(2, r) - pow3(K), m)
    with open(path, "wb") as f:
        f.write(w)
    if verbose:
        print(f"  built G(r={r}) len={m} in {time.time()-t0:.1f}s", flush=True)
    return bytes(w)


def t_prefix(m):
    """First m digits of 2^P in base 3 (via pow mod 3^m)."""
    v = pow(2, P, pow3(m))
    return to_base3_bytes(v, m)


def admissible_rhos(limit=20):
    """even, >=162, rho%486 not in {0,2,8}, 2^rho Cantor mod 3^15."""
    out = []
    r = 162
    while len(out) < limit:
        if r % 486 not in (0, 2, 8):
            v = pow(2, r, pow3(15))
            if all(d <= 1 for d in to_base3_bytes(v, 15)):
                out.append(r)
        r += 2
    return out


def has2_below(b, m=None):
    seq = b if m is None else b[:m]
    return any(d == 2 for d in seq)


def first2(b):
    for i, d in enumerate(b):
        if d == 2:
            return i
    return -1


def top_digits_decimal(r, k=50):
    """Top k ternary digits of G(r) via theta walk: G = 3^K (3^theta - 1)."""
    K = Kstar(r)
    theta = (Decimal(r) * LOG3_2) % 1
    z = pow(Decimal(3), theta) - 1          # in [0, 2)
    digs = []
    for _ in range(k):
        d = int(z)                          # 0 or 1
        digs.append(d)
        z = (z - d) * 3
    return K, digs                           # digs[0] = digit_K(G), then downward


if __name__ == "__main__":
    print("P =", P, " K*(P) =", Kstar(P), " L =", Kstar(P) + 1)
    print("admissible rhos:", admissible_rhos(8))
    print("332 admissible-check: %486 =", 332 % 486,
          " cantor15 =", all(d <= 1 for d in
                             to_base3_bytes(pow(2, 332, pow3(15)), 15)))
    print("5246 admissible-check: %486 =", 5246 % 486,
          " cantor15 =", all(d <= 1 for d in
                             to_base3_bytes(pow(2, 5246, pow3(15)), 15)))
