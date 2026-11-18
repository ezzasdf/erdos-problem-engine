#!/usr/bin/env python3
"""Experiment A — transition study of critical gaps G_q along the class q -> q+1.

    G_q = 2^{rho+Pq} - 3^{K*(rho+Pq)},   admissible rho.

Records per (rho, q):
  - clean prefix cp(G_q) (first digit 2), count of 2s, clean window [5,301)
  - top ternary digits (Decimal theta-walk)
  - transition q -> q+1: first changed digit, highest changed digit (overlap),
    number of changed digits  (bottom-aligned AND top-aligned)
  - window carry analysis of x -> 2^P x on G_q: raw convolution + carry
    propagation; verifies low-K digits of G_{q+1} == low-K digits of 2^P G_q;
    records rescue events (carry flips a would-be 2), carry-chain lengths,
    created-2 positions
  - dependence on rho (table across admissible rho)

Theory checked inline: v_3(2^P - 1) = 15  =>  2^P = 1 (mod 3^15), ord properties
=> first changed digit between any two class members is exactly 15.
"""
import sys, time, argparse
import numpy as np
from x2p_common import (P, Kstar, pow3, gword, to_base3_bytes, admissible_rhos,
                        first2, top_digits_decimal, CACHE)
import os


def word_stats(w, r, tag):
    K = Kstar(r)
    cp = first2(w)
    n2 = w.count(2)
    win = None
    if len(w) >= 301:
        win = not any(d == 2 for d in w[5:301])
    Kt, top = top_digits_decimal(r, 50)
    return dict(tag=tag, r=r, K=K, len=len(w), cp=cp, n2=n2,
                clean301=win, top=top, topK=Kt)


def print_stats(s):
    print(f"  [{s['tag']}] r={s['r']} K*={s['K']} len={s['len']} "
          f"clean_prefix={s['cp']} n2={s['n2']} win[5,301)_clean={s['clean301']}",
          flush=True)
    print(f"      top50: {''.join(map(str, s['top'][:50]))}", flush=True)


def transition(wa, wb, ra, rb, t_full, tag, W=16384):
    La, Lb = len(wa), len(wb)
    A = np.frombuffer(wa, np.uint8)
    B = np.frombuffer(wb, np.uint8)
    L = min(La, Lb)
    d = np.flatnonzero(A[:L] != B[:L])
    first = int(d[0]) if len(d) else None
    last = int(d[-1]) if len(d) else None
    nd = int(len(d))
    # top-aligned: word b is longer by off; compare b's top La digits vs a
    off = Lb - La
    dt = np.flatnonzero(A[:La] != B[off:off + La]) if off >= 0 else d
    print(f"  TRANSITION {tag}: lens {La} -> {Lb} (K* {Kstar(ra)} -> {Kstar(rb)})")
    print(f"      bottom-aligned overlap [0,{L}): first_changed={first} "
          f"highest_changed={last} n_changed={nd}")
    print(f"      top-aligned: first_changed={int(dt[0]) if len(dt) else None} "
          f"n_changed={int(len(dt))}", flush=True)

    # window carry: low-K digits of G_{q+1} should equal low digits of 2^P * G_q
    Ww = min(Kstar(ra), W, La, Lb)
    g = np.frombuffer(wa[:Ww], dtype=np.uint8).astype(np.int64)
    t = np.frombuffer(t_full[:Ww], dtype=np.uint8).astype(np.int64)
    c = np.convolve(g, t)[:Ww]
    u_in = 0
    chain = 0
    max_chain = 0
    n_chains = 0
    rescues = 0
    fails = []
    b_out = np.zeros(Ww, dtype=np.int8)
    for k in range(Ww):
        ck = int(c[k])
        b = (ck + u_in) % 3
        u = (ck + u_in) // 3
        b_out[k] = b
        if b == 2:
            fails.append(k)
        if ck % 3 == 2 and u_in > 0:
            rescues += 1
        if u > 0:
            if chain == 0:
                n_chains += 1
            chain += 1
            if chain > max_chain:
                max_chain = chain
        else:
            chain = 0
        u_in = u
    match = bool(np.array_equal(b_out, np.frombuffer(wb[:Ww], np.int8)))
    print(f"      carry window [0,{Ww}): identity(low G_{{q+1}} = 2^P G_q)={match}  "
          f"chains={n_chains} max_chain={max_chain} rescues={rescues}  "
          f"2s_created_in_window={len(fails)} first_2_at={fails[0] if fails else None}",
          flush=True)
    return dict(first=first, last=last, nd=nd, match=match, chains=n_chains,
                max_chain=max_chain, rescues=rescues, nfail=len(fails),
                firstfail=(fails[0] if fails else None), Ww=Ww)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--q2", action="store_true", help="also rho=332 q=2 (slow)")
    args = ap.parse_args()

    # theory: v_3(2^P - 1) = 15
    t15 = pow(2, P, pow3(15)) == 1
    t16 = pow(2, P, pow3(16)) != 1
    print(f"[theory] v_3(2^P-1)=15 (2^P=1 mod 3^15: {t15}, !=1 mod 3^16: {t16})")

    # full t = digits of 2^P, cached
    L = Kstar(P) + 1
    tp = os.path.join(CACHE, "t_P.b3")
    t0 = time.time()
    if os.path.exists(tp) and os.path.getsize(tp) == L:
        t_full = open(tp, "rb").read()
        print(f"[t] loaded cached 2^P word, len={L}")
    else:
        t_full = to_base3_bytes(pow(2, P), L)
        open(tp, "wb").write(t_full)
        print(f"[t] built 2^P word len={L} in {time.time()-t0:.1f}s")
    tf2 = first2(t_full)
    print(f"[t] 2^P: first2={tf2}  n2_in_first_16384={t_full[:16384].count(2)}")

    rhos = sorted(set([332, 5246] + admissible_rhos(4)))
    print(f"[rho] admissible rhos under study: {rhos}\n", flush=True)

    for rho in rhos:
        print(f"=== rho = {rho} ===", flush=True)
        qs = [0, 1, 2] if (args.q2 and rho == 332) else [0, 1]
        words = {}
        stats = {}
        for q in qs:
            r = rho + q * P
            w = gword(r, tag=f"{rho}_q{q}")
            words[q] = w
            stats[q] = word_stats(w, r, f"rho={rho} q={q}")
            print_stats(stats[q])
        for q in qs[1:]:
            transition(words[q - 1], words[q], rho + (q - 1) * P, rho + q * P,
                       t_full, f"rho={rho}: q={q-1}->{q}")
        print(flush=True)

    print("=== rho-dependence summary (cp / n2 / transition) ===", flush=True)


if __name__ == "__main__":
    main()
