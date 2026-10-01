#!/usr/bin/env python3
"""Step 2/3 follow-up: validate the sum-mass invariant and pin down its logical role.

Findings so far:
  - max_{k>=5} b_k >= 2  FAILS (persistent M=1 tail).
  - sum_{k>=5} b_k >= 2  holds with ZERO violations for K=12..15.

This script checks two remaining questions before writing findings:

  Q1. Does sum >= 2 survive at K=16 (u_16 = 28,697,856)?

  Q2. Logical role: sum >= 2 CANNOT imply {r alpha} outside phi^{-1}(C_30)
      on its own -- the target set has positive measure ~1.11*(2/3)^30, so
      equidistribution guarantees infinitely many integers with sum >= 2 that
      land INSIDE it. We verify this directly: among ordinary integers
      (not in N_K), count residues with sum >= 2 and frac inside phi^-1(C_30).
      Expected: strictly positive -> the coefficient condition is only
      meaningful JOINTLY with trailing membership r in N_K.
"""

from decimal import Decimal, getcontext
from typing import List

getcontext().prec = 200

ALPHA = Decimal(2).ln() / Decimal(3).ln()
THREE = Decimal(3)
SPECIAL = {0, 2, 8}


def continued_fraction(x: Decimal, nterms: int = 80) -> List[int]:
    a = []
    cur = x
    for _ in range(nterms):
        ai = int(cur)
        a.append(ai)
        frac = cur - ai
        if frac == 0:
            break
        cur = Decimal(1) / frac
    return a


def convergents(a: List[int]) -> List[List[int]]:
    p, q = [], []
    pm2, pm1 = 0, 1
    qm2, qm1 = 1, 0
    for ai in a:
        pi = ai * pm1 + pm2
        qi = ai * qm1 + qm2
        p.append(pi)
        q.append(qi)
        pm2, pm1, qm2, qm1 = pm1, pi, qm1, qi
    return q


def ostrowski_representation(n: int, q: List[int]) -> List[int]:
    if n == 0:
        return [0] * len(q)
    k = 0
    while k < len(q) - 1 and q[k + 1] <= n:
        k += 1
    b = [0] * len(q)
    remaining = n
    for i in range(k, -1, -1):
        if q[i] <= remaining:
            b[i] = remaining // q[i]
            remaining -= b[i] * q[i]
    return b


def u_k(K: int) -> int:
    return 2 * (3 ** (K - 1))


def compute_N_K(K: int) -> List[int]:
    period = u_k(K)
    modulus = 3 ** K
    N_K = []
    pow2_mod = 1
    for r in range(period):
        val = pow2_mod
        while val > 0 and val % 3 != 2:
            val //= 3
        if not (val > 0):
            N_K.append(r)
        pow2_mod = (pow2_mod * 2) % modulus
    return N_K


def in_phi_inv_C(frac: Decimal, L: int = 30) -> bool:
    """True iff first L ternary digits of 3^frac avoid digit 2."""
    val = THREE ** frac
    for _ in range(L):
        d = int(val)
        if d == 2:
            return False
        val = (val - d) * THREE
    return True


def main() -> None:
    q = convergents(continued_fraction(ALPHA))

    print("=" * 92)
    print("Q1. SUM-MASS INVARIANT AT K=16")
    print("=" * 92)
    K = 16
    print(f"computing N_16 (period {u_k(K):,}) ...")
    N_K = compute_N_K(K)
    nonspecial = [r for r in N_K if r not in SPECIAL]

    min_m = None
    min_s = None
    cnt_m1 = cnt_s1 = cnt_nnz1 = 0
    m1_list = []
    s1_list = []
    for r in nonspecial:
        b = ostrowski_representation(r, q)
        hi = b[5:]
        m_val = max(hi)
        s_val = sum(hi)
        nz = sum(1 for x in hi if x != 0)
        min_m = m_val if min_m is None else min(min_m, m_val)
        min_s = s_val if min_s is None else min(min_s, s_val)
        if m_val == 1:
            cnt_m1 += 1
            if len(m1_list) < 20:
                m1_list.append(r)
        if s_val == 1:
            cnt_s1 += 1
            s1_list.append(r)
        if nz == 1:
            cnt_nnz1 += 1

    print(f"|N_16 \\ {{0,2,8}}| = {len(nonspecial)}")
    print(f"  min max_(k>=5) b_k   = {min_m}   (#M==1: {cnt_m1}, examples {m1_list})")
    print(f"  min sum_(k>=5) b_k   = {min_s}   (#sum==1: {cnt_s1}, list {s1_list})")
    print(f"  #nnz==1              = {cnt_nnz1}")

    print()
    print("=" * 92)
    print("Q2. LOGICAL ROLE: sum>=2 alone vs joint with N_K membership")
    print("=" * 92)

    # scan ordinary integers r in [1, R_MAX): classify (in some N_K? just raw ints)
    R_MAX = 300000
    both = []          # sum>=2 AND inside phi^-1(C_30)  -> kills standalone implication
    sep_no_sum = 0     # separated but sum<2 (informational)
    checked = 0
    for r in range(1, R_MAX):
        b = ostrowski_representation(r, q)
        s_val = sum(b[5:])
        if s_val < 2:
            continue
        frac = (Decimal(r) * ALPHA) % 1
        checked += 1
        if in_phi_inv_C(frac, 30):
            both.append(r)

    print(f"integers r < {R_MAX:,} with sum_(k>=5) b_k >= 2 : {checked:,}")
    print(f"  of these, INSIDE phi^-1(C_30) (separation FAILS): {len(both)}")
    if both:
        print(f"  examples: {both[:10]}")
    print()
    print("=> sum>=2 by itself does NOT force {r*alpha} out of phi^-1(C_30);")
    print("   the coefficient condition only makes sense JOINTLY with r in N_K.")
    print("   Correct theorem shape:  r in N_K \\ {0,2,8}  AND  sum >= 2")
    print("   -> explicit displacement argument -> {r alpha} outside C_30 window.")


if __name__ == "__main__":
    main()
