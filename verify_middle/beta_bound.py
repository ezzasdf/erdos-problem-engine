#!/usr/bin/env python3
"""Phase 9: best-effort beta < log_3(2) heuristic + rigor analysis.

Computes the two-window counting bound
    B(x, k, K) = 2^k * (x/u_k + 1) * P_rig(K),   u_k = 2*3^(k-1),
over a grid of (x, k, K), using the exact leading-digit probability
P(f >= K) (finite sum over 2^(K-1) strings, K <= 20; convergent C*(2/3)^K
beyond) and the rigorous unconditional Phase 8 upper bound
P_rig(K) = 1.152*(2/3)^K.  Reports beta_eff(x) = ln(min B)/ln(x) against
alpha = log_3(2) and writes an auditable 12-column CSV.

This establishes the inequality on the tested grid under the stated
Weyl/equidistribution bound.  It does NOT establish a global pointwise
beta < alpha theorem.

Python stdlib only. Run from repo root.
"""

import csv
import math

ALPHA = math.log(2.0) / math.log(3.0)
C_CONV = 1.1147647951       # exact P(f>=L)/(2/3)^L, converged by L ~ 10 (Phase 8)
C_RIG = 1.152               # rigorous P(f>=L) <= C_RIG*(2/3)^L (Phase 8, unconditional)
K_EXACT_MAX = 20            # exact finite sum up to K=20; C*(2/3)^K beyond (documented policy)
K_MAX = 30
M_MIN, M_MAX = 4, 39        # x = 3^m, m in [4, 39]  (~81 .. ~4.05e18)


def u_k(k):
    return 2 * 3 ** (k - 1)


def p_exact_table():
    """P(f>=L) = sum over length-L strings s (s_0=1, rest in {0,1}) of
    log_3((t_s + 3^{1-L}) / t_s), t_s = sum_i s_i 3^{-i}.  L = 1..K_EXACT_MAX."""
    tab = {}
    for L in range(1, K_EXACT_MAX + 1):
        total = 0.0
        for m in range(2 ** (L - 1)):
            t = 1.0
            for i in range(1, L):
                if (m >> (L - 1 - i)) & 1:
                    t += 3.0 ** (-i)
            total += math.log((t + 3.0 ** (1 - L)) / t, 3)
        tab[L] = total
    return tab


def p_exact(K, tab):
    if K <= K_EXACT_MAX:
        return tab[K]
    return C_CONV * (2.0 / 3.0) ** K


def p_rigorous(K):
    return C_RIG * (2.0 / 3.0) ** K


def bound(x, k, K, pval):
    return (2.0 ** k) * (x / u_k(k) + 1.0) * pval


def beta_eff(x, bmin):
    return math.log(bmin) / math.log(x)


def main():
    tab = p_exact_table()

    print("== P(f>=K): exact (finite sum, K<=%d; C*(2/3)^K beyond) vs rigorous 1.152*(2/3)^K =="
          % K_EXACT_MAX)
    print(f"{'K':>2} {'P_exact':>14} {'P_rigorous':>14} {'ratio':>8}")
    for K in range(1, K_MAX + 1):
        pe = p_exact(K, tab)
        pr = p_rigorous(K)
        print(f"{K:>2} {pe:14.8e} {pr:14.8e} {pe / pr:8.4f}")

    rows = []
    failing = []
    for m in range(M_MIN, M_MAX + 1):
        x = 3 ** m
        k_lo = max(1, m - 8)
        k_hi = m + 8
        best_exact = None
        best_rig = None
        for k in range(k_lo, k_hi + 1):
            for K in range(1, K_MAX + 1):
                be = bound(x, k, K, p_exact(K, tab))
                br = bound(x, k, K, p_rigorous(K))
                if best_exact is None or be < best_exact[0]:
                    best_exact = (be, k, K)
                if best_rig is None or br < best_rig[0]:
                    best_rig = (br, k, K)
        Be, ke, Ke = best_exact
        Br, kr, Kr = best_rig
        beta_e = beta_eff(x, Be)
        beta_r = beta_eff(x, Br)
        rows.append({
            "x": x,
            "beta_eff_exact": beta_e,
            "beta_eff_rigorous": beta_r,
            "alpha": ALPHA,
            "alpha_minus_beta_exact": ALPHA - beta_e,
            "alpha_minus_beta_rigorous": ALPHA - beta_r,
            "k_opt_exact": ke,
            "K_opt_exact": Ke,
            "k_opt_rigorous": kr,
            "K_opt_rigorous": Kr,
            "B_exact": Be,
            "B_rigorous": Br,
        })
        if not (beta_r < ALPHA):
            failing.append(x)
        print(f"x=3^{m}  beta_eff_exact={beta_e:.6f}  beta_eff_rigorous={beta_r:.6f}  "
              f"(k,K)_exact=({ke},{Ke})  (k,K)_rig=({kr},{Kr})")

    with open("verify_middle/beta_bound.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    print("\nRIGOROUS-BOUND CHECK:")
    if failing:
        print("beta_eff < alpha on tested grid: FAIL")
        print("failing x:", failing)
        return 1
    print("beta_eff < alpha on tested grid: PASS")

    print("\nSTATUS:")
    print("This establishes the inequality for the evaluated grid under")
    print("the stated Weyl/equidistribution bound.")
    print("It does NOT establish a global pointwise beta < alpha theorem.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
