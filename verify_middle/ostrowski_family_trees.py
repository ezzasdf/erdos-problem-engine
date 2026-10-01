#!/usr/bin/env python3
"""Step 3: Saye family trees of the mass-1 lineages + displacement feature mining.

Part 1 -- family trees.
  N_{K+1} is generated from N_K by Saye's recursion: every r in N_K has
  exactly two surviving children among {r, r+u_K, r+2u_K} in N_{K+1}
  (the third branch makes ternary digit K+1 equal to 2).
  For each mass-1 residue (sum_{k>=5} b_k = 1, i.e. r = q_j + l, l <= 18)
  we trace how long its lineage stays mass-1 and where it dies.

Part 2 -- displacement features.
  The eventual proof needs an EXPLICIT bound: coefficient pattern forces a
  digit 2 within the first J leading ternary digits of 2^r, with J < 30.
  We mine which Ostrowski feature controls f2(r) = position of first digit 2
  among leading digits of 3^{frac(r alpha)}.
"""

from decimal import Decimal, getcontext
from typing import Dict, List, Tuple

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


def mass_profile(r: int, q: List[int]) -> Tuple[int, int, int, int, int]:
    """(mass, nnz, maxb, jtop, lowpart) over positions >= 5."""
    b = ostrowski_representation(r, q)
    hi = b[5:]
    nz = [(5 + i, x) for i, x in enumerate(hi) if x != 0]
    return sum(hi), len(nz), max(hi), (nz[-1][0] if nz else -1), r - sum(x * q[5 + i] for i, x in enumerate(hi))


def first_digit2_position(frac: Decimal, L: int = 30):
    val = THREE ** frac
    for i in range(L):
        d = int(val)
        if d == 2:
            return i
        val = (val - d) * THREE
    return None


def main() -> None:
    q = convergents(continued_fraction(ALPHA))
    print("q:", ", ".join(f"q[{i}]={v}" for i, v in enumerate(q[:12])))
    print()

    # ------------------------------------------------------------------ build
    print("building N_K for K=5..16 ...")
    N: Dict[int, set] = {}
    for K in range(5, 17):
        N[K] = set(compute_N_K(K))
    print("done\n")

    # sanity: Saye parent structure -- every child's parent is in N_K
    print("sanity check of Saye parent map (r' -> r' % u_K):")
    for K in range(5, 16):
        uk = u_k(K)
        ok = all((c % uk) in N[K] for c in N[K + 1])
        n_children_ok = True
        counts = {}
        for c in N[K + 1]:
            counts[c % uk] = counts.get(c % uk, 0) + 1
        bad = [p for p, cnt in counts.items() if cnt != 2]
        print(f"  K={K}: parents all in N_K: {ok};  exactly-2-children rule: "
              f"{not bad} ({len(bad)} violators)")
    print()

    # ------------------------------------------------------------- mass sets
    S: Dict[int, list] = {}
    prof: Dict[int, dict] = {}
    for K in range(5, 17):
        S[K] = sorted(r for r in N[K] if r not in SPECIAL and mass_profile(r, q)[0] == 1)

    print("=" * 92)
    print("PART 1: MASS-1 LINEAGES (r = q_j + l forms)")
    print("-" * 92)
    for K in range(5, 17):
        dec = []
        for s in S[K]:
            m, nz, mx, jtop, low = mass_profile(s, q)
            dec.append(f"{s}=q[{jtop}]+{low}")
        print(f"K={K}: |S_K| = {len(S[K]):>3}   {dec}")

    # lineage tracing: for each seed in earliest S levels, follow mass-1 descendants
    def children_map(K: int) -> Dict[int, list]:
        uk = u_k(K)
        cmap: Dict[int, list] = {}
        for c in N[K + 1]:
            cmap.setdefault(c % uk, []).append(c)
        return cmap

    print()
    print("lineage death analysis:")
    seeds = sorted(set(S[5]) | set(S[6]) | set(S[7]) | set(S[8]) |
                   set(S[9]) | set(S[10]) | set(S[11]))
    for s in seeds:
        origin = min(K for K in range(5, 17) if s in S[K])
        # walk down the tree; at each level record which descendants are mass-1
        frontier = {s}
        last_level = origin
        trace = []
        for K in range(origin, 16):
            cm = children_map(K)
            nxt_mass1 = []
            nxt_all = []
            for node in frontier:
                kids = cm.get(node % u_k(K)) if False else None
            # recompute properly: children of nodes living at level K live at K+1
            cmK = children_map(K)
            for node in sorted(frontier):
                kids = cmK.get(node, [])
                nxt_all.extend(kids)
                for kid in kids:
                    if mass_profile(kid, q)[0] == 1:
                        nxt_mass1.append(kid)
            if nxt_mass1:
                last_level = K + 1
                trace.append((K + 1, sorted(set(nxt_mass1))))
                frontier = set(nxt_mass1)
            else:
                kid_masses = sorted(mass_profile(k, q)[0] for k in nxt_all)
                print(f"  seed r={s} (origin K={origin}, form q[{mass_profile(s,q)[3]}]"
                      f"+{mass_profile(s,q)[4]}): mass-1 lineage survives through "
                      f"K={last_level}, dies entering K={K+1}")
                print(f"      final children masses at K={K+1}: {kid_masses}")
                break
        else:
            print(f"  seed r={s}: still mass-1 at K=16?!")

    print()
    print("=" * 92)
    print("PART 2: DISPLACEMENT FEATURES  f2(r) vs Ostrowski profile (K=12..15)")
    print("-" * 92)
    rows = []
    for K in (12, 13, 14, 15):
        for r in sorted(N[K]):
            if r in SPECIAL:
                continue
            m, nz, mx, jtop, low = mass_profile(r, q)
            frac = (Decimal(r) * ALPHA) % 1
            f2 = first_digit2_position(frac, 30)
            rows.append((r, K, m, nz, mx, jtop, low, f2))

    import statistics as st

    print(f"{'K':>3} {'n':>6} {'maxF2':>6} {'meanF2':>8} | corr(f2,·): "
          f"{'mass':>6} {'nnz':>6} {'maxb':>6} {'jtop':>7} {'low':>7}")
    byK: Dict[int, list] = {}
    for row in rows:
        byK.setdefault(row[1], []).append(row)
    for K in (12, 13, 14, 15):
        data = byK[K]
        f2s = [d[7] for d in data]
        feats = {
            'mass': [d[2] for d in data],
            'nnz': [d[3] for d in data],
            'maxb': [d[4] for d in data],
            'jtop': [d[5] for d in data],
            'low': [d[6] for d in data],
        }

        def pearson(xs, ys):
            n = len(xs)
            mx_, my_ = sum(xs) / n, sum(ys) / n
            sx = (sum((x - mx_) ** 2 for x in xs)) ** 0.5
            sy = (sum((y - my_) ** 2 for y in ys)) ** 0.5
            if sx == 0 or sy == 0:
                return 0.0
            return sum((x - mx_) * (y - my_) for x, y in zip(xs, ys)) / (sx * sy)

        corrs = {name: pearson(v, f2s) for name, v in feats.items()}
        print(f"{K:>3} {len(data):>6} {max(f2s):>6} {st.mean(f2s):>8.2f} | "
              + " ".join(f"{corrs[k]:>6.3f}" for k in ('mass', 'nnz', 'maxb', 'jtop'))
              + f" {corrs['low']:>7.3f}")

    # bucket table: worst f2 vs low part l (the most actionable feature?)
    print()
    print("worst-case f2 by low-part bucket l (all K=12..15 pooled):")
    print(f"{'l range':>10} {'n':>7} {'maxF2':>6} {'p99':>6}")
    pools: Dict[Tuple[int, int], list] = {}
    for row in rows:
        lo = row[6]
        b = (lo // 5) * 5
        pools.setdefault((b, b + 4), []).append(row[7])
    for bucket in sorted(pools):
        v = sorted(pools[bucket])
        p99 = v[min(len(v) - 1, int(0.99 * len(v)))]
        print(f"{f'{bucket[0]}-{bucket[1]}':>10} {len(v):>7} {max(v):>6} {p99:>6}")

    print()
    print("worst-case f2 by top active position jtop (pooled):")
    print(f"{'jtop':>5} {'n':>7} {'maxF2':>6}")
    pools2: Dict[int, list] = {}
    for row in rows:
        pools2.setdefault(row[5], []).append(row[7])
    for jt in sorted(pools2):
        print(f"{jt:>5} {len(pools2[jt]):>7} {max(pools2[jt]):>6}")


if __name__ == "__main__":
    main()
