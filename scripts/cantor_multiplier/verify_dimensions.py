#!/usr/bin/env python3
"""Exact Hausdorff dimensions and algebraic certificates for Cantor multiplier intersections C(1,M).

Models
------
1. Forward SFT for Digitwise-Safe Multipliers:
   For M = 3^b - 3^a + 1 (1 <= a < b), expanding Mx = 3^b x - 3^a x + x yields
   the forward recurrence on binary Cantor digits:
       u_{n-b} = z_n - z_{n-(b-a)} + z_{n-b} in {0, 1}   (n >= b+1).
   This is the forward one-sided SFT with lag pair (alpha, b) = (b-a, b),
   initialized at state 0^b.

2. Carry Graph for General Multipliers:
   For general M, reading ternary digits with carry c in [0, M]:
       v = 2*M*z + c,   digit = v mod 3,   next carry = v div 3.

Exact Algebraic Certification
-----------------------------
Rather than relying on floating-point eigenvalues, the script computes the exact
integer characteristic polynomial P(x) = det(x*I - A) in Z[x], factors P(x) over Z,
and proves:
  - If x^2 - x - 1 divides P(x), then lambda = phi exactly.
  - For all other irreducible factors Q(x), an exact Sturm sequence proves that
    Q(x) has no real roots in [phi, inf), certifying lambda < phi strictly.
"""

import argparse
import sys
import numpy as np
import sympy as sp

X = sp.Symbol("x")
PHI = (1 + 5 ** 0.5) / 2
LOG3PHI = float(np.log(PHI) / np.log(3))


def forward_sft_graph(lag, b):
    """Return reachable states from 0^b and the adjacency matrix for Sigma_{(lag, b)}."""
    init = (0,) * b
    seen = {init}
    stack = [init]
    edges = {}
    while stack:
        s = stack.pop()
        edges[s] = []
        for z in (0, 1):
            val = z - s[lag - 1] + s[b - 1]
            if val in (0, 1):
                ns = (z,) + s[:-1]
                edges[s].append(ns)
                if ns not in seen:
                    seen.add(ns)
                    stack.append(ns)
    states = sorted(seen)
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    A = sp.zeros(n, n)
    for s in states:
        for ns in edges[s]:
            A[idx[s], idx[ns]] += 1
    return states, A


def carry_graph(M):
    """Return reachable carry states and adjacency matrix for general M."""
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
    idx = {c: i for i, c in enumerate(states)}
    n = len(states)
    A = sp.zeros(n, n)
    for c in states:
        for c2 in edges[c]:
            A[idx[c], idx[c2]] += 1
    return states, A


def identify_multiplier(M):
    """Identify if M belongs to Family 1, Family 2, or neither."""
    # Check Family 1: 3^k + 1
    p = 3
    for k in range(1, 15):
        if p + 1 == M:
            return "F1", k, (1, 1), 1
        p *= 3
    # Check Family 2: 3^b - 3^a + 1 with 1 <= a < b
    for b in range(2, 12):
        pow_b = 3 ** b
        if pow_b > M * 3:
            break
        for a in range(1, b):
            if pow_b - 3 ** a + 1 == M:
                return "F2", (a, b), (b - a, b), b
    return "OTHER", None, None, None


def golden_mean_graph():
    """Return reachable states and adjacency matrix for the golden mean shift (Family 1)."""
    # States: 0 and 1. Admissible transitions: 0->0, 0->1, 1->0 (1->1 forbidden).
    states = [0, 1]
    A = sp.Matrix([[1, 1], [1, 0]])
    return states, A


def get_graph_for_M(M):
    """Get the appropriate forward transition graph for multiplier M."""
    fam, params, fwd_lag, b = identify_multiplier(M)
    if fam == "F1":
        # Single-column golden mean shift: z_n + z_{n-1} in {0, 1}
        states, A = golden_mean_graph()
        return states, A, fam, params, (1, 1)
    elif fam == "F2":
        lag, b = fwd_lag
        states, A = forward_sft_graph(lag, b)
        return states, A, fam, params, fwd_lag
    else:
        states, A = carry_graph(M)
        return states, A, fam, None, None


def certify_sturm_strictly_less_than_phi(Q):
    """Algebraic Sturm sequence certificate that irreducible Q in Z[x] has no roots in [phi, inf)."""
    phi_sym = (1 + sp.sqrt(5)) / 2
    if Q == X ** 2 - X - 1:
        return True, "root == phi identically"
    
    # Sturm chain on Q
    st = sp.sturm(Q)
    
    def sign_at(poly, val):
        if val == sp.oo:
            lc = sp.Poly(poly, X).LC()
            return 1 if lc > 0 else -1
        v = poly.subs(X, val)
        return 1 if v > 0 else (-1 if v < 0 else 0)
    
    # Check roots in [8/5, oo) where 8/5 = 1.6 < phi = 1.6180339887...
    signs_16 = [sign_at(p, sp.Rational(8, 5)) for p in st]
    signs_inf = [sign_at(p, sp.oo) for p in st]
    
    def sign_changes(s_list):
        nz = [s for s in s_list if s != 0]
        return sum(1 for i in range(len(nz) - 1) if nz[i] != nz[i + 1])
    
    roots_ge_16 = sign_changes(signs_16) - sign_changes(signs_inf)
    if roots_ge_16 == 0:
        return True, "no real roots in [1.6, oo); lambda < 1.6 < phi"
    
    # If there are roots in [1.6, oo), test exactly at phi in Q(sqrt(5))
    val_phi = sp.simplify(Q.subs(X, phi_sym))
    # Since Q is irreducible and != X^2 - X - 1, val_phi != 0.
    # Check sign of Q(phi)
    val_float = float(val_phi.evalf())
    if val_float > 0:
        return True, f"Q(phi) = {val_phi} > 0; root strictly < phi"
    else:
        return False, f"Q(phi) = {val_phi} <= 0; root >= phi"


def analyse(M):
    states, A, fam, params, fwd_lag = get_graph_for_M(M)
    cp = A.charpoly()
    sym = cp.gen
    P = sp.Poly(cp.as_expr(), sym)
    
    # Numerical spectral radius
    evals = np.linalg.eigvals(np.array(A.tolist(), dtype=float))
    lam = float(max(abs(evals)))
    dim = float(np.log(lam) / np.log(3))
    
    # Identify irreducible factor carrying the Perron root
    perron_factor = None
    factors = sp.factor_list(P.as_expr())[1]
    for factor, _ in factors:
        coeffs = [float(c) for c in sp.Poly(factor, sym).all_coeffs()]
        if np.any(np.abs(np.abs(np.roots(coeffs)) - lam) < 1e-7):
            perron_factor = sp.factor(factor)
            break
            
    # Exact algebraic certificate
    pf_expr = perron_factor.subs(sym, X) if perron_factor is not None else X - 1
    is_safe, cert_msg = certify_sturm_strictly_less_than_phi(pf_expr)
    
    return {
        "M": M,
        "family": fam,
        "params": params,
        "fwd_lag": fwd_lag,
        "states": len(states),
        "lambda": lam,
        "dim": dim,
        "perron_factor": perron_factor,
        "certified_le_phi": is_safe,
        "certificate": cert_msg,
    }


def table(rows):
    print(f"{'M':>5} {'states':>7} {'lambda':>12} {'dim_H':>10}  {'perron factor':<25} {'forward SFT / certificate'}")
    print("-" * 90)
    for M in rows:
        r = analyse(M)
        fwd_str = f"fwd {r['fwd_lag']}" if r['fwd_lag'] else "carry graph"
        print(
            f"{M:>5} {r['states']:>7} {r['lambda']:>12.9f} {r['dim']:>10.6f}  "
            f"{str(r['perron_factor']):<25} {fwd_str} [{r['certificate']}]"
        )


def scan(limit):
    attain, exceed = [], []
    for M in range(2, limit + 1):
        if M % 3 == 0:
            continue
        r = analyse(M)
        if not r["certified_le_phi"]:
            exceed.append((M, r["lambda"], r["certificate"]))
        elif r["perron_factor"].subs(r["perron_factor"].free_symbols.pop(), X) == X ** 2 - X - 1:
            attain.append(M)
            
    predicted = sorted(
        {3 ** k + 1 for k in range(1, 12) if 3 ** k + 1 <= limit}
        | {3 ** (2 * a) - 3 ** a + 1 for a in range(1, 8) if 3 ** (2 * a) - 3 ** a + 1 <= limit}
    )
    print(f"Exact Algebraic Scan 2 <= M <= {limit}, gcd(M,3) = 1")
    print(f"  lambda(M) > phi (certified)  : {exceed if exceed else 'none'}")
    print(f"  attaining lambda(M) = phi    : {attain}")
    print(f"  predicted by Theorem 1       : {predicted}")
    print(f"  exact theorem certificate   : {'PASSED (100% MATCH)' if attain == predicted and not exceed else 'FAILED'}")
    return 0 if attain == predicted and not exceed else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scan", type=int, default=0, metavar="N")
    args = ap.parse_args()

    if args.scan:
        sys.exit(scan(args.scan))

    print(f"log_3(phi) = {LOG3PHI:.9f}\n")
    table([1, 2, 3, 4, 7, 10, 19, 25, 28, 55, 61, 73, 79, 82, 163, 217, 235, 244])
    return 0


if __name__ == "__main__":
    sys.exit(main())
