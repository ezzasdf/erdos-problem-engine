# Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
# Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
# Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
"""Lemma 4.1 key combinatorial step: explicit injection E -> Z'.

Window k in regime [L-a+1, L-1] at length L, g = b-a,
E  = {c_(k-1)=0, c_k=0, flip_k destroys admissibility},
Z' = Z1 U Z2,  Z1 = {c_(k-1)=1, c_k=1},  Z2 = {c_(k-1)=0, c_k=1, flip_k destroys}.

Injection: non-exception u -> flip_{k-g} (g>=2) or flip_{k-1} (g=1)
lands in the "other" class (Z2 resp. Z1); exception words (primary
image inadmissible) are routed to the complementary class by a fixed
flip S of size <= 4 chosen from a finite case table keyed on the local
closure pattern (anchor positions x offsets {0,+/-a,+/-b,+/-g}), with
an MRV/backtracking assignment so all images are disjoint.

Checks per instance: range subset Z', class correctness, injectivity.
Expected: 957 ok / 0 fail for a in [2,8), b < 16, L in [2,17]
(plus noE / skip_Z skips). Re-run with larger ranges as desired.
"""
from itertools import product, combinations
from math import gcd
from collections import Counter, defaultdict


def mk(a, b):
    def ok(w):
        L = len(w)
        for i in range(L):
            zi = w[i]
            za = w[i - a] if i - a >= 0 else 0
            zb = w[i - b] if i - b >= 0 else 0
            if not (0 <= zi - za + zb <= 1):
                return False
        return True
    return ok


def run(a_max=8, b_max=16, L_max=17):
    res = Counter()
    fails = []
    for a in range(2, a_max):
        for b in range(a + 1, b_max):
            if gcd(a, b) != 1:
                continue
            g = b - a
            OFF = (0, -a, -b, a, b, a - b, b - a)
            ok = mk(a, b)
            for L in range(2, L_max):
                U = set(w for w in product((0, 1), repeat=L) if ok(w))

                def zt(w, p, L=L):
                    return w[p] if 0 <= p < L else 0

                def cv(w, m, g=g, L=L):
                    return zt(w, m, L) ^ zt(w, m - g, L)

                def flip(w, ps):
                    v = list(w)
                    for p in ps:
                        v[p] ^= 1
                    return tuple(v)

                for k in range(max(1, L - a + 1), L):
                    bp = {'km1': k - 1, 'km1g': k - 1 - g, 'kk': k,
                          'kg': k - g, 'kga': k - g + a, 'km2g': k - 2 * g,
                          'ka': k - a, 'kb': k - b}
                    inb = {n: p for n, p in bp.items() if 0 <= p < L}
                    if 'kk' not in inb or 'km1' not in inb:
                        res['skip_pos'] += 1
                        continue
                    E = [w for w in U
                         if cv(w, k - 1) == 0 and cv(w, k) == 0
                         and flip(w, [k]) not in U]
                    if not E:
                        res['noE'] += 1
                        continue
                    Z1 = set(w for w in U
                             if cv(w, k - 1) == 1 and cv(w, k) == 1)
                    Z2 = set(w for w in U
                             if cv(w, k - 1) == 0 and cv(w, k) == 1
                             and flip(w, [k]) not in U)
                    if g == 1:
                        pmap, tgt_nont, tgt_exc = k - 1, 'Z1', 'Z2'
                    else:
                        if 'kg' not in inb:
                            res['skip_kg'] += 1
                            continue
                        pmap, tgt_nont, tgt_exc = k - g, 'Z2', 'Z1'
                    TG = {'Z1': Z1, 'Z2': Z2}
                    if not (Z1 and Z2):
                        res['skip_Z'] += 1
                        continue
                    relpos = sorted(set(
                        [bp[n] for n in inb] +
                        [bp[n] + d for n in inb for d in (a, b)
                         if 0 <= bp[n] + d < L]))
                    clo = [(n, d) for n in bp for d in OFF]
                    nonexc = []
                    exc = defaultdict(list)
                    okall = True
                    for w in E:
                        if flip(w, [pmap]) in U:
                            v = flip(w, [pmap])
                            want = (1, 1) if tgt_nont == 'Z1' else (0, 1)
                            if (cv(v, k - 1), cv(v, k)) != want or v not in TG[tgt_nont]:
                                okall = False
                                fails.append(('nonmap', a, b, L, k, g))
                                break
                            nonexc.append(w)
                        else:
                            pat = tuple(zt(w, bp[n] + d, L)
                                        if 0 <= bp[n] + d < L else None
                                        for n, d in clo)
                            exc[pat].append(w)
                    if not okall:
                        res['fail'] += 1
                        continue
                    used = {flip(w, [pmap]) for w in nonexc}
                    pcand = {}
                    for pat, ws in exc.items():
                        lst = []
                        for sz in (1, 2, 3, 4):
                            for S in combinations(relpos, sz):
                                im = [flip(w, list(S)) for w in ws]
                                if all(v in TG[tgt_exc] for v in im) \
                                        and len(set(im)) == len(ws):
                                    lst.append((S, im))
                            if len(lst) >= 4:
                                break
                        if not lst:
                            okall = False
                            fails.append(('noS', a, b, L, k, g, len(ws)))
                            break
                        pcand[pat] = lst
                    if not okall:
                        res['fail'] += 1
                        continue

                    def solve(remaining, used):
                        if not remaining:
                            return {}
                        best, bestfree = None, None
                        for p in remaining:
                            free = [(S, im) for S, im in pcand[p]
                                   if not (set(im) & used)]
                            if not free:
                                return None
                            if bestfree is None or len(free) < len(bestfree):
                                best, bestfree = p, free
                                if len(free) == 1:
                                    break
                        for S, im in bestfree:
                            r = solve([p for p in remaining if p != best],
                                      used | set(im))
                            if r is not None:
                                r[best] = S
                                return r
                        return None

                    rule = solve(list(exc), used)
                    if rule is None:
                        res['fail'] += 1
                        fails.append(('bt', a, b, L, k, g))
                        continue
                    imgs = {w: flip(w, [pmap]) for w in nonexc}
                    for pat, ws in exc.items():
                        S = list(rule[pat])
                        for w in ws:
                            imgs[w] = flip(w, S)
                    if not set(imgs.values()) <= (Z1 | Z2) or \
                            len(set(imgs.values())) != len(E):
                        res['final_fail'] += 1
                        fails.append(('fin', a, b, L, k, g))
                        continue
                    res['ok'] += 1
    return res, fails


if __name__ == '__main__':
    r, f = run()
    print('H injection certificate:', dict(r))
    print('fails:', f[:10])
    assert not f, f
