#!/usr/bin/env python3
"""Route 1 Phase A: exhaustive census of the mass-1 birth/death process.

Node classes at level K (r in N_K, K >= 1):
  SP : r in {0,2,8}                      (special; mass 0 by low part)
  Z  : mass(r) = 0 and r not special     (r <= 18; only exists for K <= 4)
  O  : mass(r) = 1                       (form q_j + l, j >= 5, l <= 18)
  T  : mass(r) >= 2

Edges: r' in N_{K+1} has parent p = r' mod u_K and edge label i = r' // u_K
in {0,1,2} (self/shift1/shift2). Saye's lemma gives exactly 2 children per
parent; the killed branch is determined by
    d_{K+1}(2^r) + i*d_1(r) =/= 2 (mod 3),   d_1(r) = 1 if r even else 2.

Rules under test:
  R2 : a shifted child (i >= 1) of an O node is never O.
  R3 : every O node whose parent is not O (a "birth") has parent in SP.
       (user's claim C, checked exhaustively with exceptions listed)

Also produced:
  - complete birth table (every birth into O ever, K=2..16)
  - complete death table (every O occurrence whose self-child failed)
  - survival depth D(f) vs reach K_r(f) for all forms f = q_j + l, j=5..80
  - accident heuristic: expected number of range-restricted survivors vs 11 observed
"""

from decimal import Decimal, getcontext
from math import log, ceil
from typing import Dict, List, Tuple

getcontext().prec = 300

ALPHA = Decimal(2).ln() / Decimal(3).ln()
SPECIAL = {0, 2, 8}


def continued_fraction(x: Decimal, nterms: int = 120) -> List[int]:
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
    q = []
    qm2, qm1 = 1, 0
    for ai in a:
        qi = ai * qm1 + qm2
        q.append(qi)
        qm2, qm1 = qm1, qi
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


def make_class(q: List[int]):
    def classify(r: int) -> str:
        if r in SPECIAL:
            return 'SP'
        m = sum(ostrowski_representation(r, q)[5:])
        if m == 0:
            return 'Z'
        if m == 1:
            return 'O'
        return 'T'
    return classify


def main() -> None:
    q = convergents(continued_fraction(ALPHA))
    classify = make_class(q)

    print("building N_K for K=1..16 ...")
    N: Dict[int, set] = {}
    for K in range(1, 17):
        N[K] = set(compute_N_K(K))
    print("done\n")

    # ---------------------------------------------------------- class census
    print("=" * 96)
    print("CLASS CENSUS |N_K| by class")
    print("-" * 96)
    print(f"{'K':>3} {'u_K':>10} {'SP':>4} {'Z':>4} {'O':>4} {'T':>6} {'total':>7}")
    for K in range(1, 17):
        c = {'SP': 0, 'Z': 0, 'O': 0, 'T': 0}
        for r in N[K]:
            c[classify(r)] += 1
        print(f"{K:>3} {u_k(K):>10} {c['SP']:>4} {c['Z']:>4} {c['O']:>4} "
              f"{c['T']:>6} {len(N[K]):>7}")

    # --------------------------------------------- R2: shifted child of O -> O?
    print()
    print("=" * 96)
    print("R2: SHIFTED CHILDREN OF O NODES  (any child with i>=1 and class O)")
    print("-" * 96)
    r2_violations = []
    shifted_mass_table = []
    for K in range(1, 16):
        uk = u_k(K)
        buckets: Dict[int, list] = {}
        for c_ in N[K + 1]:
            buckets.setdefault(c_ % uk, []).append(c_)
        for r in N[K]:
            if classify(r) != 'O':
                continue
            kids = buckets.get(r % 0 if False else r, []) if False else buckets.get(r, [])
            kids = buckets.get(r, [])
            for kid in kids:
                i = kid // uk
                kc = classify(kid)
                if i >= 1:
                    shifted_mass_table.append((K, r, i, kid, kc))
                    if kc == 'O':
                        r2_violations.append((K, r, i, kid))
    n_shift = len(shifted_mass_table)
    print(f"shifted edges out of O nodes (transitions 1->2 .. 15->16): {n_shift}")
    print(f"R2 violations (shifted child of O lands in O): {len(r2_violations)}")
    for v in r2_violations:
        K, r, i, kid = v
        print(f"   transition {K}->{K+1}: parent {r}, edge i={i}, child {kid}")
    # distribution of shifted-child classes by transition
    from collections import Counter
    dist = Counter((K, kc) for K, r, i, kid, kc in shifted_mass_table)
    print("\nshifted-child class counts by transition:")
    for K in sorted({t[0] for t in dist}):
        line = ", ".join(f"{kc}:{dist[(K,kc)]}" for kc in ('SP','Z','O','T') if dist.get((K,kc)))
        print(f"  {K}->{K+1}: {line}")

    # ------------------------------------------------- R3: births into O
    print()
    print("=" * 96)
    print("R3: ALL BIRTHS INTO O (parent class != O), transitions 1->2 .. 15->16")
    print("-" * 96)
    births = []
    for K in range(1, 16):
        uk = u_k(K)
        for r in N[K + 1]:
            if classify(r) != 'O':
                continue
            p = r % uk
            i = r // uk
            pc = classify(p)
            if pc != 'O':
                births.append((K + 1, r, p, i, pc))
    print(f"total births into O: {len(births)}")
    print(f"{'K':>3} {'child':>8} {'parent':>8} {'i':>2} {'parentClass':>12}")
    for K, r, p, i, pc in births:
        print(f"{K:>3} {r:>8} {p:>8} {i:>2} {pc:>12}")

    # ------------------------------------------- death table (self-child fails)
    print()
    print("=" * 96)
    print("DEATH EVENTS of O nodes (self-child fails entering K+1)")
    print("-" * 96)
    deaths = []
    for K in range(1, 16):
        uk = u_k(K)
        buckets: Dict[int, list] = {}
        for c_ in N[K + 1]:
            buckets.setdefault(c_ % uk, []).append(c_)
        for r in N[K]:
            if classify(r) != 'O':
                continue
            kids = buckets.get(r, [])
            ii = sorted(kid // uk for kid in kids)
            if 0 not in ii:
                masses = [sum(ostrowski_representation(kid, q)[5:]) for kid in kids]
                deaths.append((K + 1, r, masses))
    print(f"{'died entering':>14} {'node':>8}  childrenMasses")
    for K, r, ms in deaths:
        print(f"{K:>14} {r:>8}  {ms}")

    # ------------------------------- symbolic birth classification + heuristic
    print()
    print("=" * 96)
    print("SURVIVAL DEPTH D(q_j+l) vs REACH K_r, j=5..80, l=0..18")
    print("-" * 96)

    def B_K(r: int, K: int) -> bool:
        val = pow(2, r, 3 ** K)
        while val > 0 and val % 3 != 2:
            val //= 3
        return val == 0

    def reach(r: int) -> int:
        return max(1, int(ceil(log(max(r / 2.0, 1.0), 3))) + 1)

    violators = []
    expected_acc = 0.0
    ncand = 0
    for j in range(5, 81):
        Kr = reach(q[j])
        for l in range(19):
            f = q[j] + l
            ncand += 1
            D = 0
            for K in range(1, 71):
                if B_K(f, K):
                    D = K
                else:
                    break
            if D >= Kr:
                violators.append((j, l, f, D, Kr))
            # accident expectation: P(B_{Kr}) approx (1/2)(2/3)^(Kr-1)
            if j >= 9:
                expected_acc += 0.5 * (2.0 / 3.0) ** (Kr - 1)
    print(f"range-restricted survivors among forms (j=5..80): {len(violators)}")
    print(f"{'j':>3} {'l':>3} {'f':>12} {'D':>4} {'Kr':>4}")
    for j, l, f, D, Kr in violators:
        print(f"{j:>3} {l:>3} {f:>12} {D:>4} {Kr:>4}")
    print(f"\ncandidates probed: {ncand}")
    print(f"expected accidental survivors for j >= 9 (heuristic sum): "
          f"{expected_acc:.2f}")
    print(f"observed survivors with j >= 9: "
          f"{sum(1 for v in violators if v[0] >= 9)}")

    print()
    print("=" * 96)
    print("VERDICT INPUT")
    print("-" * 96)
    early = [b for b in births if b[0] <= 5]
    late = [b for b in births if b[0] >= 6]
    late_nonsp = [b for b in late if b[4] != 'SP']
    print(f"births at transitions entering K<=5 : {len(early)} (all listed above)")
    print(f"births at transitions entering K>=6 : {len(late)}, "
          f"of which non-SP parent: {len(late_nonsp)}")
    if late_nonsp:
        for b in late_nonsp:
            print("   VIOLATES claim C:", b)


if __name__ == "__main__":
    main()
