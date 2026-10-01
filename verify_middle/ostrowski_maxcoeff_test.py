#!/usr/bin/env python3
"""Step 2 checkpoint test: stronger Ostrowski invariant max_{k>=5} b_k(r) >= 2.

Question A (kill or confirm): for every non-special r in N_K \\ {0,2,8},
K = 12..15, does M(r) := max_{k>=5} b_k(r) satisfy M(r) >= 2?
The previously formalized axiom only asserts M(r) >= 1, which is weak because
q_5 = 19 already forces r >= 19.

Recorded outputs:
  1. minimum of M(r) over non-special residues
  2. counterexamples with M(r) == 1 (and M(r) == 0)
  3. the r attaining the minimum
  4. coefficient distribution as K grows
  5. mathematical consequence test: does M(r) >= 2 force
     {r*alpha} outside phi^{-1}(C_30)?  (first 30 ternary digits of 3^{frac}
     contain a digit 2)

No Lean axioms are touched here -- pure data analysis first.
"""

from collections import Counter
from decimal import Decimal, getcontext
from typing import Dict, List, Optional, Tuple

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


def convergents(a: List[int]) -> Tuple[List[int], List[int]]:
    p, q = [], []
    pm2, pm1 = 0, 1
    qm2, qm1 = 1, 0
    for ai in a:
        pi = ai * pm1 + pm2
        qi = ai * qm1 + qm2
        p.append(pi)
        q.append(qi)
        pm2, pm1, qm2, qm1 = pm1, pi, qm1, qi
    return p, q


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
    """All r in [0, u_K) whose last K ternary digits of 2^r avoid digit 2."""
    period = u_k(K)
    modulus = 3 ** K
    N_K = []
    pow2_mod = 1
    for r in range(period):
        val = pow2_mod
        has_digit_2 = False
        while val > 0:
            if val % 3 == 2:
                has_digit_2 = True
                break
            val //= 3
        if not has_digit_2:
            N_K.append(r)
        pow2_mod = (pow2_mod * 2) % modulus
    return N_K


def fractional_part(n: int) -> Decimal:
    return (Decimal(n) * ALPHA) % 1


def leading_digit2_position(frac: Decimal, L: int) -> Optional[int]:
    """Position of first digit 2 among first L ternary digits of 3^frac.

    None means all L digits avoid 2 (i.e. frac in phi^{-1}(C_L))."""
    val = THREE ** frac
    for i in range(L):
        d = int(val)
        if d == 2:
            return i
        val = (val - d) * THREE
    return None


def analyze_K(K: int, q: List[int], K_MIN_POS: int = 5) -> dict:
    N_K = compute_N_K(K)
    nonspecial = [r for r in N_K if r not in SPECIAL]

    rows = []
    for r in nonspecial:
        b = ostrowski_representation(r, r and q or q)
        m_val = max(b[K_MIN_POS:])
        frac = fractional_part(r)
        first2 = leading_digit2_position(frac, 30)
        rows.append({
            'r': r,
            'M': m_val,
            'separated': first2 is not None,   # {r alpha} NOT in phi^{-1}(C_30)
            'first2': first2,
            'b': b,
        })

    m_dist = Counter(row['M'] for row in rows)
    min_m = min(m_dist)
    argmin = sorted(row['r'] for row in rows if row['M'] == min_m)
    m1_rows = [row for row in rows if row['M'] == 1]
    m0_rows = [row for row in rows if row['M'] == 0]

    # weaker invariant sanity check (the current axiom content): M >= 1
    weaker_violations = [row['r'] for row in rows if row['M'] == 0]

    # consequence cross-tabulation
    grp_m2 = [row for row in rows if row['M'] >= 2]
    grp_m1 = m1_rows
    sep_m2 = sum(1 for row in grp_m2 if row['separated'])
    sep_m1 = sum(1 for row in grp_m1 if row['separated'])

    return {
        'K': K,
        'n_nonspecial': len(rows),
        'm_dist': m_dist,
        'min_m': min_m,
        'argmin': argmin[:20],
        'm1_examples': [(row['r'], row['first2']) for row in m1_rows[:20]],
        'm0_examples': [(row['r'], row['first2']) for row in m0_rows[:20]],
        'weaker_violations': weaker_violations[:20],
        'n_m2': len(grp_m2),
        'sep_m2': sep_m2,
        'n_m1': len(grp_m1),
        'sep_m1': sep_m1,
        'rows': rows,
    }


def main() -> None:
    a_cf = continued_fraction(ALPHA)
    _, q_conv = convergents(a_cf)

    print("=" * 92)
    print("STEP 2 TEST: STRONGER OSTROWSKI INVARIANT  max_{k>=5} b_k(r) >= 2")
    print("=" * 92)
    print()
    print(f"alpha = log_3(2) = {ALPHA}")
    print()
    print("Convergent denominators q_k (index from 0):")
    print("  " + ", ".join(f"q[{i}]={qi}" for i, qi in enumerate(q_conv[:12])))
    print(f"  -> q[5] = {q_conv[5]} (checkpoint convention)")
    print()

    results: Dict[int, dict] = {}
    for K in (10, 11, 12, 13, 14, 15):
        print(f"computing K={K} ...")
        results[K] = analyze_K(K, q_conv)

    print()
    for K in (10, 11, 12, 13, 14, 15):
        res = results[K]
        dist_sorted = sorted(res['m_dist'].items())
        print("-" * 92)
        print(f"K={K}:  |N_K \\ {{0,2,8}}| = {res['n_nonspecial']}")
        print(f"  distribution of M(r) = max_(k>=5) b_k(r): "
              + ", ".join(f"M={m}: {c}" for m, c in dist_sorted))
        print(f"  MINIMUM M(r)          = {res['min_m']}")
        print(f"  attained at r         = {res['argmin']}")
        print(f"  counterexamples M==1  = {res['n_m1']}"
              + (f"  examples: {res['m1_examples']}" if res['n_m1'] else ""))
        print(f"  counterexamples M==0  = {len(res['m0_examples'])}"
              + (f"  examples: {res['m0_examples']}" if res['m0_examples'] else ""))
        print(f"  weaker invariant (M>=1) violations: {res['weaker_violations']}")
        print(f"  consequence: M>=2 group size {res['n_m2']}, separated "
              f"{res['sep_m2']}  (failures: {res['n_m2'] - res['sep_m2']})")
        print(f"             M==1 group size {res['n_m1']}, separated "
              f"{res['sep_m1']}  (failures: {res['n_m1'] - res['sep_m1']})")

    print()
    print("=" * 92)
    print("VERDICT SUMMARY")
    print("=" * 92)
    all_ok = all(results[K]['min_m'] >= 2 for K in (12, 13, 14, 15))
    print(f"  M(r) >= 2 universal for K=12..15 : {all_ok}")

    total_m2 = sum(results[K]['n_m2'] for K in (12, 13, 14, 15))
    total_m2_sep = sum(results[K]['sep_m2'] for K in (12, 13, 14, 15))
    total_m1 = sum(results[K]['n_m1'] for K in (12, 13, 14, 15))
    total_m1_sep = sum(results[K]['sep_m1'] for K in (12, 13, 14, 15))
    print(f"  M>=2 -> separation from phi^-1(C_30): "
          f"{total_m2_sep}/{total_m2} failures={total_m2 - total_m2_sep}")
    print(f"  M==1 -> separation                    : "
          f"{total_m1_sep}/{total_m1} failures={total_m1 - total_m1_sep}")


if __name__ == "__main__":
    main()
