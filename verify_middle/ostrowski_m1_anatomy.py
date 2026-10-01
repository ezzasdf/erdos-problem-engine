#!/usr/bin/env python3
"""Step 2 follow-up: anatomy of the M(r)=1 exceptions.

The main test showed max_{k>=5} b_k(r) >= 2 FAILS universally (a thin
persistent tail of M==1 residues exists at every K). Before abandoning the
Ostrowski direction we characterize the exceptions:

  A. full Ostrowski representations of the persistent M=1 residues
     (which positions are active, which coefficient equals 1);
  B. alternative strengthenings:
       nnz(k>=5) >= 2   (# distinct active positions)
       sum(k>=5) >= 2   (total mass above q_5)
  C. persistence: is the M=1 set nested across K (do exceptions survive
     into every deeper N_K)?

Pure data -- no axioms.
"""

from collections import Counter
from decimal import Decimal, getcontext
from typing import Dict, List

getcontext().prec = 200

ALPHA = Decimal(2).ln() / Decimal(3).ln()
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


def main() -> None:
    q = convergents(continued_fraction(ALPHA))
    print("q:", ", ".join(f"q[{i}]={v}" for i, v in enumerate(q[:12])))
    print()

    # collect M=1 sets for K=10..15 plus reps
    m1_sets: Dict[int, set] = {}
    reps: Dict[int, List[int]] = {}

    for K in range(10, 16):
        N_K = compute_N_K(K)
        m1 = []
        for r in N_K:
            if r in SPECIAL:
                continue
            b = ostrowski_representation(r, q)
            if max(b[5:]) == 1:
                m1.append(r)
                reps.setdefault(r, b)
        m1_sets[K] = set(m1)

    print("=" * 92)
    print("C. PERSISTENCE of the M=1 exception set")
    print("-" * 92)
    prev: set = set()
    for K in range(10, 16):
        cur = m1_sets[K]
        carried = len(cur & prev) if prev else 0
        new = sorted(cur - prev) if prev else sorted(cur)
        lost = sorted(prev - cur) if prev else []
        print(f"K={K}: |M=1| = {len(cur)}  (carried from K-1: {carried}, "
              f"new: {len(new)}, dropped: {len(lost)})")
        if new:
            print(f"      new this level: {new}")
        if lost:
            print(f"      dropped this level: {lost}")
        prev = cur
    core = m1_sets[10]
    for K in range(11, 16):
        core = core & m1_sets[K]
    print(f"\ncore exceptions present at EVERY K=10..15 ({len(core)}): {sorted(core)}")

    print()
    print("=" * 92)
    print("A. OSTROWSKI ANATOMY of the core / representative M=1 residues")
    print("-" * 92)
    show = sorted(core) if core else sorted(m1_sets[15])
    for r in show:
        b = reps[r]
        active_hi = [(k, b[k]) for k in range(5, len(b)) if b[k] != 0]
        lo_part = sum(b[i] * q[i] for i in range(5))
        print(f"  r={r}: active k>=5 -> {active_hi}")
        print(f"         low part (<q_5*1) = {lo_part}, "
              f"low coeff slice b[0:5] = {b[0:5]}")

    print()
    print("=" * 92)
    print("B. ALTERNATIVE STRENGTHENINGS over non-special N_K, K=10..15")
    print("-" * 92)
    header = f"{'K':>3} | {'|NS|':>6} | {'minM':>4} {'#M=1':>5} | " \
             f"{'minNnz':>6} {'#nnz=1':>6} | {'minSum':>6} {'#sum=1':>6}"
    print(header)
    for K in range(10, 16):
        N_K = compute_N_K(K)
        stats = {"M": [], "nnz": [], "s": []}
        cnt = Counter()
        for r in N_K:
            if r in SPECIAL:
                continue
            b = ostrowski_representation(r, q)
            hi = b[5:]
            m_val = max(hi)
            nz = sum(1 for x in hi if x != 0)
            s_val = sum(hi)
            stats["M"].append(m_val)
            stats["nnz"].append(nz)
            stats["s"].append(s_val)
            cnt[(m_val == 1, nz == 1, s_val == 1)] += 1
        print(f"{K:>3} | {len(stats['M']):>6} | {min(stats['M']):>4} "
              f"{cnt[(True, False, False)]:>5} | "
              f"{min(stats['nnz']):>6} {cnt[(False, True, False)]:>6} | "
              f"{min(stats['s']):>6} {cnt[(True, True, True)]:>6}")
    print()
    print("(columns after minNnz/minSum count residues attaining exactly that "
          "minimum; note nnz counts DISTINCT active positions, sum counts total mass)")


if __name__ == "__main__":
    main()
