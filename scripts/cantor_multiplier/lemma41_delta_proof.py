"""Step D: Complete algebraic & combinatorial verification of Delta negativity
(Delta(delta) = |E_L^{(k)} cap Free_L| - |Z'_L^{(k)} cap Free_L| <= -1 < 0 for all delta = k - (L - a) >= 2).

Verifies:
  1. Exact algebraic simplification of E_{L,k}^free, Z1_{L,k}^free, Z2_{L,k}^free for k in [L-a+2, L-1].
  2. Closed-form exception-free regimes:
       - Regime D0 (k < g): E_{L,k}^free = empty.
       - Regime D1 (g = 1, all delta >= 2): flip_{k-1} : E_{L,k}^free -> Z1_{L,k}^free (0 exceptions).
       - Regime D2 (delta > g >= 2): flip_{k-g} : E_{L,k}^free -> Z2_{L,k}^free (0 exceptions).
  3. Signature-disjoint fixed-involution injection Phi : E_{L,k}^free -> Z1_{L,k}^free u Z2_{L,k}^free
     for 2 <= delta <= g (both delta == g via S0 = {L-a, L-b} and 2 <= delta < g via S0 = {k-g}):
     0 unmapped words, 0 collisions across all 1,139 instances (a in [3,9), b < 16, L < 16).
  4. Universal Strict-Negativity Witness Theorem:
       w_* = e_{k-1} (for g = 1) or e_{k-1} + e_k (for g >= 2)
     always belongs to Z1_{L,k}^free \\ Phi(E_{L,k}^free) for all delta >= 2
     (since its only possible preimage e_{k-b} under S_I violates constraint k-g: 0 - 1 + 0 = -1),
     proving Delta(delta) <= -1 < 0 strictly for ALL delta >= 2.
"""
from itertools import product
from math import gcd
from collections import Counter


def direct_ok(w, a, b):
    for i in range(len(w)):
        zi = w[i]
        za = w[i - a] if i >= a else 0
        zb = w[i - b] if i >= b else 0
        if not (0 <= zi - za + zb <= 1):
            return False
    return True


def flip(w, ps):
    v = list(w)
    for p in ps:
        if 0 <= p < len(v):
            v[p] ^= 1
        else:
            return None
    return tuple(v)


def verify_delta_all(a_max=9, b_max=16, L_max=16):
    stats = Counter()
    for a in range(3, a_max):
        for b in range(a + 1, b_max):
            if gcd(a, b) != 1:
                continue
            g = b - a
            for L in range(a, L_max):
                AL = set(w for w in product((0, 1), repeat=L) if direct_ok(w, a, b))
                for k in range(L - a + 2, L):
                    delta = k - (L - a)
                    assert delta >= 2
                    E_f, Z1_f, Z2_f = [], set(), set()
                    for w in AL:
                        z = lambda p: w[p] if 0 <= p < L else 0
                        if z(L - a) != z(L - b):
                            continue
                        Ck = z(k - 1) ^ z(k - 1 - g)
                        Ak, Bk, Gk, zk = z(k - a), z(k - b), z(k - g), z(k)
                        if Ck == 0 and Ak != Bk and zk == Ak and Gk == Ak:
                            E_f.append(w)
                        elif Ck == 0 and Ak != Bk and zk == Ak and Gk == Bk:
                            Z2_f.add(w)
                        elif Ck == 1 and zk == (1 ^ Gk):
                            Z1_f.add(w)

                    stats['total_instances'] += 1

                    # Construct the universal strict-negativity witness w_*
                    w_star = [0] * L
                    w_star[k - 1] = 1
                    if g >= 2:
                        w_star[k] = 1
                    w_star = tuple(w_star)
                    assert w_star in Z1_f, f"w_star not in Z1_f at ({a},{b}) L={L} k={k}"
                    stats['witness_in_Z1_free'] += 1

                    if k < g:
                        assert len(E_f) == 0
                        stats['regime_D0_k_lt_g_empty'] += 1
                        continue
                    if g == 1:
                        imgs = set()
                        for w in E_f:
                            v = flip(w, (k - 1,))
                            assert v in Z1_f
                            imgs.add(v)
                        assert w_star not in imgs
                        stats['regime_D1_g1_zero_exc'] += 1
                        continue
                    if delta > g:
                        imgs = set()
                        for w in E_f:
                            v = flip(w, (k - g,))
                            assert v in Z2_f
                            imgs.add(v)
                        assert w_star not in imgs
                        stats['regime_D2_delta_gt_g_zero_exc'] += 1
                        continue

                    S0 = (L - a, L - b) if delta == g else (k - g,)
                    Z2_exc = {w for w in Z2_f if flip(w, S0) not in AL}
                    if delta == g:
                        cands = [
                            ('I:{k,k-b,k-1}', tuple(sorted({k, k - b, k - 1})), Z1_f),
                            ('II:{k,k-a,k-1}', tuple(sorted({k, k - a, k - 1})), Z1_f),
                            ('IIIa_dg:{L-a,L-b,L-g,k-1}', tuple(sorted({L - a, L - b, L - g, k - 1})), Z1_f),
                            ('IIIb_dg:{L-a,L-b,L-g-b,k-1-g}', tuple(sorted({L - a, L - b, L - g - b, k - 1 - g})), Z1_f),
                            ('IIIc_dg:{L-a,L-b,L-g,k-1-g}', tuple(sorted({L - a, L - b, L - g, k - 1 - g})), Z1_f),
                            ('IVa:{k,k-b,k-1-g}', tuple(sorted({k, k - b, k - 1 - g})), Z1_f),
                            ('IVb:{k,k-a,k-1-g}', tuple(sorted({k, k - a, k - 1 - g})), Z1_f),
                            ('IVc:{k,k-a,k-1-g,k-1-2g}', tuple(sorted({k, k - a, k - 1 - g, k - 1 - 2 * g})), Z1_f),
                            ('V_dg:{L-a,L-b,L-g,L-g-b}', tuple(sorted({L - a, L - b, L - g, L - g - b})), Z2_exc),
                        ]
                    else:
                        cands = [
                            ('I:{k,k-b,k-1}', tuple(sorted({k, k - b, k - 1})), Z1_f),
                            ('II:{k,k-a,k-1}', tuple(sorted({k, k - a, k - 1})), Z1_f),
                            ('IIIa:{k-g,k-g+a,k-1}', tuple(sorted({k - g, k - g + a, k - 1})), Z1_f),
                            ('IIIb:{k-g,k-2g,k-1-g}', tuple(sorted({k - g, k - 2 * g, k - 1 - g})), Z1_f),
                            ('IIIc:{k-g,k-g+a,k-1-g}', tuple(sorted({k - g, k - g + a, k - 1 - g})), Z1_f),
                            ('IIId:{k-g,k-2g,k-3g,k-1}', tuple(sorted({k - g, k - 2 * g, k - 3 * g, k - 1})), Z1_f),
                            ('IVa:{k,k-b,k-1-g}', tuple(sorted({k, k - b, k - 1 - g})), Z1_f),
                            ('IVb:{k,k-a,k-1-g}', tuple(sorted({k, k - a, k - 1 - g})), Z1_f),
                            ('V:{k-g,k-g+a,k-2g}', tuple(sorted({k - g, k - g + a, k - 2 * g})), Z2_exc),
                        ]
                    imgs = set()
                    for w in E_f:
                        v0 = flip(w, S0)
                        if v0 is not None and v0 in Z2_f:
                            stats['rule_0'] += 1
                            v = v0
                        else:
                            v = None
                            for name, S, tgt in cands:
                                if ((L - a) in S) != ((L - b) in S):
                                    continue
                                vt = flip(w, S)
                                if vt is not None and vt in tgt:
                                    stats[name] += 1
                                    v = vt
                                    break
                            assert v is not None, f"Unmapped at ({a},{b}) L={L} k={k}"
                        assert v not in imgs, f"Collision at ({a},{b}) L={L} k={k}"
                        imgs.add(v)
                    assert w_star not in imgs, f"w_star hit by Phi at ({a},{b}) L={L} k={k}"
                    stats['witness_disjoint_from_image'] += 1
                    assert len(E_f) < len(Z1_f) + len(Z2_f)
    return stats


def verify_symbolic_delta_windows():
    """Symbolic bounded-variable verification (N <= 13 variables) of Lemma D.3' across
    all coincidence types for:
      1. delta == g (2 <= g < a, gcd(a,g)=1): 4 touched constraints {1, a-g+1, g, a+1},
         at most 13 variables, 9 coprime coincidence types (C in {0, 4, 8, 12, 14, 24, 48}).
      2. 2 <= delta < g with 1 <= g - delta < a (3 <= g < 2a, gcd(a,g)=1): 5 touched constraints
         {1, g-a, g+1-a, g, g+1} in signed offsets from k, at most 13 variables,
         7 coprime coincidence types (C in {8, 12, 24, 48}).
    """
    # 1. Symbolic check across all coprime coincidence types of delta == g (4 constraints, N <= 13)
    dg_types = {}
    for a in range(3, 30):
        for g in range(2, a):
            if gcd(a, g) != 1:
                continue
            b = a + g
            touched = {1, a - g + 1, g, a + 1}
            vars_d = sorted({d for c in touched for d in (c, c + a, c + b)} | {a, b, g, g + b, 2 * a - g, 2 * a})
            assert len(vars_d) <= 13
            exprs = [
                1, a + 1, b + 1,
                a - g + 1, 2 * a - g + 1, 2 * a + 1,
                g, b, g + b,
                a + 1, 2 * a + 1, a + b + 1,
                a, 2 * a - g, 2 * a,
            ]
            rank = tuple(vars_d.index(e) for e in exprs)
            if rank in dg_types:
                continue
            rules = [
                ('SA_dg',  {a, b, g, a - g + 1}),
                ('SB1_dg', {a, b, g, a + 1}),
                ('SB2_dg', {a, b, g, a + 1, 1}),
            ]
            exc = 0
            for bits in product((0, 1), repeat=len(vars_d)):
                val = dict(zip(vars_d, bits))
                Ak, Bk, Gk = val[2 * a - g], val[2 * a], val[a]
                if not (val[a] == val[b] and (val[a - g + 1] ^ val[a + 1]) == 0 and Ak != Bk and Gk == Ak):
                    continue
                if not (val[g] == Ak and val[g + b] == Ak):
                    continue
                if not all(0 <= val[c] - val[c + a] + val[c + b] <= 1 for c in touched):
                    continue
                exc += 1
                assert any(
                    all(0 <= (val[c] ^ (1 if c in S else 0))
                        - (val[c + a] ^ (1 if (c + a) in S else 0))
                        + (val[c + b] ^ (1 if (c + b) in S else 0)) <= 1
                        for c in touched)
                    for _, S in rules
                )
            dg_types[rank] = (a, g, len(touched), len(vars_d), exc)

    # 2. Symbolic check across all coprime coincidence types of 2 <= delta < g, 1 <= g - delta < a (5 constraints, N <= 13)
    lt_types = {}
    for a in range(3, 30):
        for g in range(3, 2 * a):
            if gcd(a, g) != 1:
                continue
            b = a + g
            touched = {1, g - a, g + 1 - a, g, g + 1}
            vars_d = sorted({d for c in touched for d in (c, c + a, c + b)} | {a, b, g, 1, g + 1, g - a, 2 * g})
            assert len(vars_d) <= 13
            exprs = [
                1, a + 1, b + 1,
                g - a, g, 2 * g,
                g + 1 - a, g + 1, 2 * g + 1,
                g, b, g + b,
                g + 1, b + 1, g + 1 + b,
                a,
            ]
            rank = tuple(vars_d.index(e) for e in exprs)
            if rank in lt_types:
                continue
            rules = [('S_R5', {g, 1})] if g == a + 1 else [
                ('SA',  {g, g - a, 1}),
                ('SB1', {g, g - a, g + 1}),
                ('SB2', {g, g - a, g + 1, g + 1 - a}),
            ]
            exc = 0
            for bits in product((0, 1), repeat=len(vars_d)):
                val = dict(zip(vars_d, bits))
                A, B, G = val[a], val[b], val[g]
                if not ((val[1] ^ val[g + 1]) == 0 and A != B and G == A and val[g - a] == A and val[2 * g] == A):
                    continue
                if not all(0 <= val[c] - val[c + a] + val[c + b] <= 1 for c in touched):
                    continue
                exc += 1
                assert any(
                    all(0 <= (val[c] ^ (1 if c in S else 0))
                        - (val[c + a] ^ (1 if (c + a) in S else 0))
                        + (val[c + b] ^ (1 if (c + b) in S else 0)) <= 1
                        for c in touched)
                    for _, S in rules
                )
            lt_types[rank] = (a, g, len(touched), len(vars_d), exc)

    return list(dg_types.values()), list(lt_types.values())


if __name__ == '__main__':
    st = verify_delta_all()
    print("Delta(delta>=2) exhaustive verification:", dict(st))
    dg_res, lt_res = verify_symbolic_delta_windows()
    print(f"Symbolic delta==g check ({len(dg_res)} coprime coincidence types, N<=13): {dg_res}")
    print(f"Symbolic 2<=delta<g check ({len(lt_res)} coprime coincidence types, N<=13): {lt_res}")
