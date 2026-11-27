#!/usr/bin/env python3
"""Exact Hausdorff dimensions for Cantor multiplier intersections C(1,M).

Model
-----
Write x in the Cantor set as x = sum_j 2*z_j 3^{-(j+1)} with z_j in {0,1}.
Then
    M*x = sum_j (2*M*z_j) 3^{-(j+1)},
so the coefficient sequence 2*M*z_j must be normalised.  Reading from the
least significant digit with carry c, one step is

    v = 2*M*z + c,   digit = v mod 3,   next carry = v div 3,

and M*x lies in the Cantor set iff every produced digit is 0 or 2.  The carry
is confined to [0, M], so this is a finite graph.  The entropy of the set of
admissible z-sequences is the Perron root lambda(M) of the adjacency matrix,
and dim_H C(1,M) = log(lambda(M)) / log(3).

The graph is deterministic (each state has at most one edge per label), so the
number of length-n paths exceeds the number of length-n words by at most a
constant factor |states|; the exponential growth rate is unaffected.

Usage
-----
    python3 verify_dimensions.py               # paper table
    python3 verify_dimensions.py --scan 2000   # exhaustive check up to M
"""

import argparse
import sys

import numpy as np
import sympy as sp

X = sp.Symbol("x")
PHI = (1 + 5 ** 0.5) / 2
LOG3PHI = float(np.log(PHI) / np.log(3))


def carry_graph(M):
    """Return the reachable carry states and the adjacency matrix over Z."""
    edges = {c: [] for c in range(M + 1)}
    for c in range(M + 1):
        for z in (0, 1):
            v = 2 * M * z + c
            if v % 3 in (0, 2):
                edges[c].append(v // 3)
    seen, stack = {0}, [0]
    while stack:
        for c2 in edges[stack.pop()]:
            if c2 not in seen:
                seen.add(c2)
                stack.append(c2)
    states = sorted(seen)
    index = {c: i for i, c in enumerate(states)}
    A = sp.zeros(len(states), len(states))
    for c in states:
        for c2 in edges[c]:
            A[index[c], index[c2]] += 1
    return states, A


def analyse(M):
    states, A = carry_graph(M)
    cp = A.charpoly()
    sym = cp.gen
    charpoly = sp.Poly(cp.as_expr(), sym)
    # numpy is far more robust than sympy.nroots for the higher-degree cases
    lam = float(max(abs(np.linalg.eigvals(np.array(A.tolist(), dtype=float)))))
    dim = float(np.log(lam) / np.log(3))
    # irreducible factor carrying the Perron root: the one with a root at lambda
    perron_factor = None
    for factor, _ in sp.factor_list(charpoly.as_expr())[1]:
        coeffs = [float(c) for c in sp.Poly(factor, sym).all_coeffs()]
        if np.any(np.abs(np.abs(np.roots(coeffs)) - lam) < 1e-8):
            perron_factor = sp.factor(factor)
            break
    return {
        "M": M,
        "states": len(states),
        "lambda": lam,
        "dim": dim,
        "charpoly": charpoly,
        "perron_factor": perron_factor,
    }


def table(rows):
    print(f"{'M':>5} {'states':>6} {'lambda':>12} {'dim_H':>10}  perron factor")
    for M in rows:
        r = analyse(M)
        print(
            f"{M:>5} {r['states']:>6} {r['lambda']:>12.9f} {r['dim']:>10.6f}"
            f"  {r['perron_factor']}"
        )


def scan(limit):
    attain, exceed = [], []
    for M in range(2, limit + 1):
        if M % 3 == 0:
            continue
        lam = analyse(M)["lambda"]
        if lam > PHI + 1e-9:
            exceed.append((M, lam))
        elif abs(lam - PHI) < 1e-9:
            attain.append(M)
    predicted = sorted(
        {3 ** k + 1 for k in range(1, 12) if 3 ** k + 1 <= limit}
        | {3 ** (2 * a) - 3 ** a + 1 for a in range(1, 8) if 3 ** (2 * a) - 3 ** a + 1 <= limit}
    )
    print(f"scan 2 <= M <= {limit}, gcd(M,3) = 1")
    print(f"  lambda(M) > phi            : {exceed if exceed else 'none'}")
    print(f"  attaining lambda(M) = phi  : {attain}")
    print(f"  predicted by Theorem 1     : {predicted}")
    print(f"  match                      : {attain == predicted}")
    return 0 if attain == predicted and not exceed else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scan", type=int, default=0, metavar="N")
    args = ap.parse_args()

    if args.scan:
        sys.exit(scan(args.scan))

    print(f"log_3(phi) = {LOG3PHI:.9f}\n")
    # table of the paper, plus the two cospectral curiosities
    table([1, 2, 3, 4, 7, 10, 19, 25, 28, 55, 61, 73, 79, 82, 163, 217, 235, 244])
    return 0


if __name__ == "__main__":
    sys.exit(main())
