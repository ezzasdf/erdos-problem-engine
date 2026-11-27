#!/usr/bin/env python3
# Copyright (c) 2026 Ezzeldin Ashraf Mohamed Shafey Wahba. All rights reserved.
# Released under the PolyForm Strict License 1.0.0 as described in the file LICENSE-CODE.
# Authors: Ezzeldin Ashraf Mohamed Shafey Wahba
"""Experiment B v2 — where the * 2^P carry automaton actually constrains.

Findings from v1 (x2p_automaton.py, kept for the record):
  - input phase NEVER dead-ends: t_0 = 1 (2^P = 1 mod 3), so output options at
    step i are {v, v+1} mod 3 which always contain a non-2 -> from any history
    at least one choice of a_i keeps b_i in {0,1}.  Consequence: for EVERY n
    there is a 0/1 input of length n with 2^P x clean on ALL of [0, n)
    (indeed infinite 3-adic solutions exist, by Konig + this extension
    property -> nonemptiness of Lagarias's C(1, 2^P) at the 3-adic level).
  - branching is 2 exactly when (f[i]+carry) = 0 mod 3, else 1 (forced bit).
  - the constraint lives entirely in the TAIL [n, m): v1 m=301 runs:
      n=150 (tail 151): 1 survivor / 3e6 nodes;  n=286 (tail 15): 2036;
      n=301 (tail 0): abundant.
  - random (unconditioned) inputs die at mean depth 17.6.

v2 measures:
  1. entropy of the valid shift: exact path counts at m=n for small n
     (= Lagarias Perron-Frobenius growth rate of the automaton).
  2. random valid-path sampling: forced/free bit rate, carry and rescue
     statistics along surviving paths (the carry-chain-length data).
  3. tail survival P(tail [n,n+W) clean | valid input) for W in {...} -> the
     forbidden-pattern / obstruction curve; dense survivor examples;
     full-word check if any W=600 survivor appears.
"""
import argparse, time
import numpy as np
from x2p_common import P, pow3, t_prefix, to_base3_bytes


def exact_counts(t, ns, budget):
    print("=== 1. exact valid-path counts (m = n) ===", flush=True)
    rows = []
    for n in ns:
        tt = np.asarray(t[:n], dtype=np.int64)
        f = np.zeros(n + 1, dtype=np.int64)
        nodes = [0]
        leaves = [0]
        hit = [False]
        u = [0]

        def rec2(i):
            nodes[0] += 1
            if nodes[0] > budget:
                hit[0] = True
                return
            if i == n:
                leaves[0] += 1
                return
            fi = int(f[i])
            uin = u[0]
            t0 = int(tt[0])
            for a in (0, 1):
                c = fi + a * t0
                b = (c + uin) % 3
                if b > 1:
                    continue
                if a:
                    f[i + 1:n] += tt[1:n - i]
                u[0] = (c + uin) // 3
                rec2(i + 1)
                u[0] = uin
                if a:
                    f[i + 1:n] -= tt[1:n - i]
                if hit[0]:
                    return

        t0 = time.time()
        rec2(0)
        h = (np.log2(leaves[0]) / n) if (leaves[0] and not hit[0]) else None
        print(f"n={n:<4} nodes={nodes[0]:<10} leaves={leaves[0]}"
              f"{' (budget)' if hit[0] else ''}  "
              f"h=log2(leaves)/n={h if h is None else round(h,4)}  "
              f"({time.time()-t0:.1f}s)", flush=True)
        if h is not None:
            rows.append((n, leaves[0], h))
    return rows


def sample_valid_paths(t, n, Ws, S, seed=11):
    """Random valid paths; at leaf measure tails [n, n+W)."""
    m = n + max(Ws) + 4
    tt = np.asarray(t[:m], dtype=np.int64)
    rng = np.random.default_rng(seed)
    forced = 0
    free = 0
    rescues = 0
    maxcarry = 0
    tail_hits = {W: 0 for W in Ws}
    tail_first = {W: [] for W in Ws}
    dense_word = None
    dense_ones = -1
    S_done = 0
    for s in range(S):
        f = np.zeros(m + 1, dtype=np.int64)
        u = 0
        word = bytearray(n)
        mc = 0
        rc = 0
        alive = True
        for i in range(n):
            fi = int(f[i])
            v0 = (fi + u) % 3          # b for a=0
            v1 = (v0 + 1) % 3          # b for a=1 (t_0=1)
            opts = [a for a in (0, 1) if (v0 if a == 0 else v1) <= 1]
            if len(opts) == 1:
                forced += 1
            else:
                free += 1
            a = opts[int(rng.integers(len(opts)))]
            word[i] = a
            c = fi + a
            if c % 3 == 2 and u > 0:
                rc += 1
            if a:
                f[i + 1:m] += tt[1:m - i]
            u = (c + u) // 3
            if u > mc:
                mc = u
        # tails
        x = 0
        for i in range(n - 1, -1, -1):
            x = 3 * x + word[i]
        ok_all = {}
        for W in Ws:
            mod = pow3(n + W)
            y = (pow(2, P, mod) * x) % mod
            d = to_base3_bytes(y, n + W)
            fp = -1
            for k in range(n, n + W):
                if d[k] == 2:
                    fp = k
                    break
            if fp < 0:
                tail_hits[W] += 1
            else:
                tail_first[W].append(fp - n)
        ones = sum(word)
        if ones > dense_ones:
            dense_ones = ones
            dense_word = bytes(word)
        if mc > maxcarry:
            maxcarry = mc
        rescues += rc
        S_done += 1
    print(f"  samples={S_done}  forced_bits={forced} free_bits={free} "
          f"(free_frac={free/(forced+free):.3f})  mean_rescues/path="
          f"{rescues/S:.1f}  max_carry_seen={maxcarry}", flush=True)
    for W in Ws:
        h = tail_hits[W]
        fl = tail_first[W]
        import statistics as st
        med = int(st.median(fl)) if fl else None
        print(f"  tail [n,n+{W:>3}): clean={h}/{S} ({h/S:.3e})  "
              f"first2_rel_median={med}", flush=True)
    return dense_word, tail_hits


def full_word_check(x):
    y = pow(2, P) * x
    L = 0
    vv = y
    while vv:
        vv //= 3
        L += 1
    d = to_base3_bytes(y, L)
    pos = next((i for i, v in enumerate(d) if v == 2), -1)
    n2 = d.count(2)
    print(f"  FULL WORD: len={L} first2={pos} n2={n2}", flush=True)
    return pos


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--S", type=int, default=3000)
    args = ap.parse_args()

    print("[identity] 2^P = 1 mod 3^15:", pow(2, P, pow3(15)) == 1,
          " != 1 mod 3^16:", pow(2, P, pow3(16)) != 1,
          " (t_0 = 1:", pow(2, P, 3) == 1, ")")
    t = t_prefix(1100)
    print(f"[t] prefix {len(t)} digits; first2={next(i for i,d in enumerate(t) if d==2)}",
          flush=True)

    exact_counts(t, [8, 12, 16, 20, 22], budget=12_000_000)

    print("\n=== 2/3. random valid paths + tail survival ===", flush=True)
    for n, S, Ws in [(150, args.S, [30, 60, 151, 301, 600]),
                     (400, max(1000, args.S // 2), [60, 301, 600])]:
        print(f"-- n={n}, S={S}, tails={Ws}", flush=True)
        dense, hits = sample_valid_paths(t, n, Ws, S)
        ones = sum(dense)
        print(f"  densest sampled path: ones={ones}/{n}", flush=True)
        if hits[600] > 0:
            print("  (a W=600-clean path exists -> full-word check needed)",
                  flush=True)
        else:
            xv = 0
            for i in range(n - 1, -1, -1):
                xv = 3 * xv + dense[i]
            mod = pow3(n + 600)
            y = (pow(2, P, mod) * xv) % mod
            d = to_base3_bytes(y, n + 600)
            fp = next((k for k in range(n, n + 600) if d[k] == 2), -1)
            print(f"  densest path full-tail probe [n,n+600): first2={fp}",
                  flush=True)


if __name__ == "__main__":
    main()
