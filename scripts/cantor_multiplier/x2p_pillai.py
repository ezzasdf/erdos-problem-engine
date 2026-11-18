#!/usr/bin/env python3
"""Magnitude/Pillai + continued-fraction session for the critical gap.

Q1 answered: digit_{K*}(G) = 0 iff theta_r = {r log_3 2} < log_3 2 (density 0.63093).
This script attacks the two OPEN rows:

R3 magnitude: hc (case a) forces G <= (3^K* - 1)/2   [exact: 2^{r+1}+1 <= 3^{K*+1}]
   (b)-case forces G <= (3^{K*+1} - 1)/2             [exact: 2^{r+1} <= 5*3^K* - 1]
   => theta windows [0, log_3(3/2)] and [log_3 2, log_3(5/2)], measure 0.369 + 0.203.
   Verify: necessity exact on all A(r) in range; density of windows vs A-density;
   class rotation hits windows i.o. (exact integer mod-1 arithmetic);
   Pillai margins: observed relative gaps vs Baker-style floors, absolute G vs 2^{dr}.

R4 CF: convergents of log_3 2 — do the known (a)-instances sit at denominators?
   where would a future instance's archimedean constraint be weakest?
   CF of alpha = {P log_3 2} governs best within-class hits.
"""
import sys, time, math
from decimal import Decimal, getcontext

P = 162 * 59049
getcontext().prec = 70
LOG3_2 = Decimal(2).ln() / Decimal(3).ln()
HC_WIN = (Decimal(3) / Decimal(2)).ln() / Decimal(3).ln()          # log_3(3/2)
B_WIN_LO = LOG3_2                                                  # log_3 2
B_WIN_HI = (Decimal(5) / Decimal(2)).ln() / Decimal(3).ln()        # log_3(5/2)
ALPHA = (Decimal(P) * LOG3_2) % 1

L_F = 0.63092975357145743709952710268360      # log_3 2 (float)
F_F = 0.36907074953695070158476838334010      # log_3(3/2)
BH_F = 0.8340324452479551663940759334         # log_3(5/2)


def Kstar(r):
    return int(Decimal(r) * LOG3_2)


def has2_below(v, m):
    for _ in range(m):
        if v % 3 == 2:
            return True
        v //= 3
    return False


def is_A(r):
    K = Kstar(r)
    if K == 0:
        return False
    if has2_below(pow(2, r, 3 ** min(K, 45)), min(K, 45)):
        return False
    if K > 45 and has2_below(pow(2, r, 3 ** min(K, 140)), min(K, 140)):
        return False
    if K > 140 and has2_below(pow(2, r, 3 ** K), K):
        return False
    return True


def cf(a, nterms=22):
    x, out = a, []
    for _ in range(nterms):
        i = int(x)
        out.append(i)
        fr = x - i
        if fr == 0:
            break
        x = 1 / fr
    return out


def convergents(terms):
    out, p0, p1, q0, q1 = [], 0, 1, 1, 0
    for a in terms:
        p, q = a * p1 + p0, a * q1 + q0
        out.append((p, q))
        p0, p1, q0, q1 = p1, p, q1, q
    return out


def part1_digit_identity(R=5000):
    """Exact integer verification of digit_{K*}(G) in {0,1} and the theta formula."""
    print(f"=== P1 digit_{{K*}}(G) identity (r in [2,{R}], exact bigints) ===", flush=True)
    n, K, t3 = 4, 1, 3              # r=2: 2^2, K*=1, 3^1
    bad = zeros = 0
    for r in range(2, R + 1):
        if r > 2:
            n <<= 1
            while t3 * 3 <= n:
                t3 *= 3
                K += 1
            assert K == Kstar(r), (r, K, Kstar(r))
        digit = n // t3 - 1                       # = digit_{K*}(2^r - 3^{K*})
        theta = (Decimal(r) * LOG3_2) % 1
        formula = 0 if theta < LOG3_2 else 1
        if digit not in (0, 1) or digit != formula:
            bad += 1
            if bad <= 5:
                print(f"  MISMATCH r={r} digit={digit} formula={formula}", flush=True)
        zeros += (digit == 0)
    exp0 = 0.63093 * (R - 1)
    print(f"  mismatches: {bad}/{R - 1}   digit=0 count: {zeros} (expect ~{exp0:.0f})", flush=True)
    return bad == 0


def part2_windows(N=10 ** 5, NF=10 ** 6):
    """Necessity of magnitude windows for A(r); window densities vs A density."""
    print(f"\n=== P2 magnitude windows ===", flush=True)
    n, K, t3 = 8, 1, 3              # r=2: n = 2^{r+1} = 8, t3 = 3^{K*}
    As = []
    for r in range(2, N + 1):
        win_a = (n + 1 <= t3 * 3)                 # 2^{r+1}+1 <= 3^{K*+1}
        win_b = (n <= 5 * t3 - 1)                 # 2^{r+1} <= 5*3^{K*} - 1
        if is_A(r):
            theta = (Decimal(r) * LOG3_2) % 1
            case = 'a' if theta < LOG3_2 else 'b'
            ok = win_a if case == 'a' else win_b
            As.append((r, case, ok))
        n <<= 1
        K2 = Kstar(r + 1)
        while K < K2:
            t3 *= 3
            K += 1
    ok = all(x[2] for x in As)
    print(f"  A-instances r<={N}: {[(r, c) for r, c, _ in As]}", flush=True)
    print(f"  exact-window necessity for each: {[(r, c, o) for r, c, o in As]}  -> ALL HOLD: {ok}", flush=True)

    zhc = zb = 0
    for r in range(1, NF + 1):
        th = (r * L_F) % 1
        if th <= F_F:
            zhc += 1
        if L_F <= th < BH_F:
            zb += 1
    print(f"  theta-window densities over r<=1e6 (identity-verified in P1):", flush=True)
    print(f"    hc   [0, log_3(3/2)]        : {zhc / NF:.5f}  (theory {F_F:.5f})", flush=True)
    print(f"    (b)  [log_3 2, log_3(5/2))  : {zb / NF:.5f}  (theory {BH_F - L_F:.5f})", flush=True)
    print(f"    combined A-necessary window : {(zhc + zb) / NF:.5f}  (theory {F_F + BH_F - L_F:.5f})",
          flush=True)
    print(f"    vs A-density observed ~3e-6 -> necessary-but-weak; digit-freeness binds:", flush=True)
    print(f"    #2-free G <= (3^K*-1)/2 is exactly 2^K*  => within-window density (2/3)^K*",
          flush=True)


def part3_cf():
    print(f"\n=== P3 continued fractions ===", flush=True)
    terms = cf(LOG3_2, 24)
    conv = convergents(terms)
    print(f"  CF log_3 2 = {terms}", flush=True)
    print(f"  {'p/q':<14} {'q':<8} {'theta_q':<16} {'|q*log_3 2 - p|':<16}", flush=True)
    qhit = {}
    for p, q in conv[1:]:
        dist = abs(Decimal(q) * LOG3_2 - p)
        th = (Decimal(q) * LOG3_2) % 1
        qhit[q] = float(th)
        print(f"  {str(p) + '/' + str(q):<14} {q:<8} {float(th):<16.10f} {float(dist):<16.3e}",
              flush=True)
    for r in (2, 6, 8):
        tag = f"denominator of convergent (theta={qhit[r]:.6f})" if r in qhit else \
              f"NOT a convergent denominator; theta={(Decimal(r) * LOG3_2) % 1}"
        print(f"  instance r={r}: {tag}", flush=True)
    qs = [q for p, q in conv]
    nxt = [q for q in qs if q > 8][:8]
    print(f"  next convergent denominators after 8 (weakest-theta candidates): {nxt}", flush=True)
    for q in nxt[:6]:
        if is_A(q):
            print(f"    r={q}: A(r) TRUE!", flush=True)
    ta = cf(ALPHA, 20)
    ca = convergents(ta)
    print(f"  CF alpha={{P log_3 2}} = {ta}", flush=True)
    print(f"  alpha convergent denominators: {[q for p, q in ca][:16]}", flush=True)
    return qs


def part4_class(Q=10 ** 6, rhos=(332, 1134)):
    """Exact integer mod-1 rotation along class; window hits; min theta; Pillai margins."""
    print(f"\n=== P4 class rotation (q <= {Q}) ===", flush=True)
    S = 10 ** 70
    alpha_int = int(ALPHA * S + Decimal('0.5'))
    L_i, F_i, B_i = int(LOG3_2 * S), int(HC_WIN * S), int(B_WIN_HI * S)
    for rho in rhos:
        cur = int(((Decimal(rho) * LOG3_2) % 1) * S + Decimal('0.5'))
        first_hc = first_b = None
        minv, minq = S + 1, -1
        cnt_hc = cnt_b = 0
        for q in range(1, Q + 1):
            cur += alpha_int
            if cur >= S:
                cur -= S
            if cur <= F_i:
                cnt_hc += 1
                if first_hc is None:
                    first_hc = q
            if L_i <= cur < B_i:
                cnt_b += 1
                if first_b is None:
                    first_b = q
            if cur < minv:
                minv, minq = cur, q
        th_min = minv / S
        r_min = rho + P * minq
        rel_gap = th_min * 1.09861228866810969139524523692      # theta * ln 3
        print(f"  rho={rho}: hc hits {cnt_hc} (exp {F_F * Q:.0f}) first q={first_hc}; "
              f"(b) hits {cnt_b} (exp {(BH_F - L_F) * Q:.0f}) first q={first_b}", flush=True)
        print(f"    min theta = {th_min:.6e} at q={minq}  (Dirichlet inhom. bound 1/Q = {1 / Q:.0e})",
              flush=True)
        print(f"    r = rho+P*q = {r_min:.4e}; relative gap ~ {rel_gap:.3e} (= {rel_gap * 3 ** 0:.1e}); "
              f"Baker-style floor r^-C: C=1 -> {1 / r_min:.1e}, C=2 -> {1 / r_min ** 2:.1e}", flush=True)
        print(f"    margin vs C=2 floor: {rel_gap * r_min ** 2:.3e} (>>1 => consistent)", flush=True)


def part5_pillai_margins(R=10 ** 6, top=6):
    """Smallest-theta r in [9,R]; exact G; margins vs 2^{d r} candidates."""
    print(f"\n=== P5 Pillai margins (r in [9,{R}]) ===", flush=True)
    cands = sorted(((r * L_F) % 1, r) for r in range(9, R + 1))[:top]
    print(f"  {'r':<8} {'theta':<12} {'log10 G':<10} {'2^{{0.05r}} log10':<18} {'margin'}", flush=True)
    for th, r in cands:
        K = Kstar(r)
        G = pow(2, r) - pow(3, K)
        lG = math.log10(G)
        lB = 0.05 * r * 0.30103
        print(f"  {r:<8} {th:<12.3e} {lG:<10.1f} {lB:<18.1f} 10^{lG - lB:.0f}x", flush=True)
    print("  => gaps sit ABOVE any 2^{0.05r}-style bound by hundreds of digits;", flush=True)
    print("     Pillai-type magnitude bounds cannot contradict A/hc.", flush=True)


def main():
    t0 = time.time()
    ok = part1_digit_identity(int(sys.argv[1]) if len(sys.argv) > 1 else 5000)
    part2_windows()
    part3_cf()
    part4_class()
    part5_pillai_margins()
    print(f"\ntotal {time.time() - t0:.0f}s   identity_ok={ok}", flush=True)


if __name__ == '__main__':
    main()
