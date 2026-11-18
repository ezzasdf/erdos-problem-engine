#!/usr/bin/env python3
"""Option (a): exhaustive top-16-bit feasibility sweep for tail survival.

Question: can choosing the TOP 16 input bits (with a fixed random valid bulk
history on [0, n-16)) rescue tail [n, n+W)?  The boundary mechanism claims the
tail's first digits are dominated by the bulk sum, so top-block control should
be powerless — this measures it exactly.

Per prefix history (n=150): enumerate ALL 65536 top-blocks, keep those that are
input-valid on [n-16, n), propagate carry into the tail, classify tail survival
and first-2 position.  Control: geometric (2/3)^w decay.
"""
import argparse, collections, time
import numpy as np
from x2p_common import P, t_prefix, pow3, to_base3_bytes


def random_valid_path(t, n, rng, m):
    tt = t
    f = np.zeros(m + 1, dtype=np.int64)
    a = np.zeros(n, dtype=np.int8)
    u = 0
    u_at = np.zeros(n + 1, dtype=np.int64)
    for i in range(n):
        u_at[i] = u
        v0 = (int(f[i]) + u) % 3
        valid_a = [a_ for a_ in (0, 1)
                   if (v0 if a_ == 0 else (v0 + 1) % 3) <= 1]
        a_ = valid_a[int(rng.integers(len(valid_a)))]
        a[i] = a_
        c = int(f[i]) + a_
        if a_:
            f[i + 1:m + 1] += tt[1:m + 1 - i]
        u = (c + u) // 3
    u_at[n] = u
    return a, u_at


def sweep(n, W, nsplit, n_prefixes, seed):
    t = t_prefix(n + W + 4)
    tt = np.asarray(t, dtype=np.int64)
    m = n + W
    rng = np.random.default_rng(seed)
    Nc = 1 << nsplit
    block = ((np.arange(Nc, dtype=np.uint32)[:, None]
              >> np.arange(nsplit)) & 1).astype(np.int64)  # (Nc, nsplit)

    hist_rel = collections.Counter()
    tot_valid = 0
    tot_clean = {10: 0, W: 0}
    valid_fracs = []
    best_rel = []
    t0 = time.time()
    for pr in range(n_prefixes):
        a, u_at = random_valid_path(tt, n, rng, m)
        split = n - nsplit
        carry0 = int(u_at[split])

        # base arrays: contributions of bulk bits j < split
        fstate = np.zeros(m + 1, dtype=np.int64)
        for j in range(split):
            if a[j]:
                fstate[j + 1:m + 1] += tt[1:m + 1 - j]
        base_in = fstate[split:split + nsplit].copy()   # (nsplit,)
        base_tail = fstate[n:n + W].copy()              # (W,)

        # candidate state
        valid = np.ones(Nc, dtype=bool)
        u = np.full(Nc, carry0, dtype=np.int64)
        f_in = np.broadcast_to(base_in, (Nc, nsplit)).copy()
        f_tail = np.broadcast_to(base_tail, (Nc, W)).copy()

        for p in range(nsplit):
            ap = block[:, p]
            c = f_in[:, p] + ap
            raw = c + u
            b = raw % 3
            valid &= (b <= 1)
            u = raw // 3
            if p + 1 < nsplit:
                f_in[:, p + 1:] += ap[:, None] * tt[None, 1:nsplit - p]
            f_tail += ap[:, None] * tt[None, nsplit - p:nsplit - p + W][:, :W]

        # tail propagation (only meaningful for input-valid candidates)
        uend = u.copy()
        rel = np.full(Nc, -1, dtype=np.int64)
        alive = valid.copy()
        uu = uend
        for k in range(W):
            raw = f_tail[:, k] + uu
            bk = raw % 3
            newly = alive & (bk == 2)
            rel[newly] = k
            alive &= (bk <= 1)
            uu = raw // 3
        rel[~valid] = -1
        rel[(rel < 0) & valid] = W  # clean all W

        nv = int(valid.sum())
        tot_valid += nv
        clean_full = int((rel[valid] == W).sum()) if nv else 0
        clean10 = int((rel[valid] >= 10).sum()) if nv else 0
        tot_clean[W] += clean_full
        tot_clean[10] += clean10
        valid_fracs.append(nv / Nc)
        for r in rel[valid]:
            hist_rel[int(r)] += 1
        if nv:
            best_rel.append(int(rel[valid].max()))

        # sanity: the actual path's block must be valid; cross-check tail via pow
        idx = 0
        for p in range(nsplit):
            idx |= int(a[split + p]) << p
        if not valid[idx]:
            print(f"  !! prefix {pr}: actual path block NOT valid (bug)")
        else:
            xv = 0
            for i in range(n - 1, -1, -1):
                xv = 3 * xv + int(a[i])
            mod = pow3(n + W)
            yy = (pow(2, P, mod) * xv) % mod
            dd = to_base3_bytes(yy, n + W)
            fp = next((k - n for k in range(n, n + W) if dd[k] == 2), W)
            if fp != int(rel[idx]):
                print(f"  !! prefix {pr}: tail mismatch pow vs automaton "
                      f"{fp} vs {int(rel[idx])}")
            else:
                pass

        print(f"  prefix {pr}: valid={nv}/{Nc} ({nv/Nc:.3f})  clean{W}="
              f"{clean_full}  clean>=10={clean10}  best_rel="
              f"{int(rel[valid].max()) if nv else '-'}  "
              f"carry0={carry0}", flush=True)

    print(f"\n=== top-{nsplit} sweep: n={n} W={W} prefixes={n_prefixes} "
          f"({time.time()-t0:.1f}s) ===")
    print(f"total valid completions: {tot_valid} "
          f"(mean frac {np.mean(valid_fracs):.3f})")
    print(f"tail clean over all W={W}: {tot_clean[W]}   clean>=10: "
          f"{tot_clean[10]}   control (2/3)^W={((2/3)**W):.2e} * valid = "
          f"{tot_valid*((2/3)**W):.1f}")
    tot = sum(hist_rel.values())
    cum = 0
    print("first2_rel distribution among valid (rel: count, P(>=rel)):")
    for r in sorted(hist_rel):
        c = hist_rel[r]
        cum += c
        if r <= 15 or r == W or c:
            print(f"  rel={r:>3}: {c:>7}  P(>={r})={(tot - (cum - c))/tot:.4f}"
                  + (f"   control (2/3)^{r}={((2/3)**r):.4f}" if r < W else ""))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=150)
    ap.add_argument("--W", type=int, default=30)
    ap.add_argument("--nsplit", type=int, default=16)
    ap.add_argument("--P", dest="npre", type=int, default=12)
    args = ap.parse_args()
    sweep(args.n, args.W, args.nsplit, args.npre, seed=7)


if __name__ == "__main__":
    main()
