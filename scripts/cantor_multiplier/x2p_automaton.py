#!/usr/bin/env python3
"""Experiment B — the sharp test: carry automaton induced by multiplication by 2^P.

Question: can an arbitrarily long 0/1 ternary input word x produce an output word
2^P * x whose digits are all in {0,1}?

Layer 1 (identity):  2^P = 1 + 3^15 * M   (v_3(2^P - 1) = 15), so the product
    y = 2^P x = x + 3^15 * M x  — the automaton is an addition/carry machine
    whose interaction begins exactly at position 15 (the G7 window origin).

Layer 2 (windowed / 3-adic):  DFS over input bits a_0, a_1, ... (low to high);
    at step i, c_i = sum_{j<i} a_j t_{i-j} + a_i t_0 is final, output digit
    b_i = (c_i + carry) mod 3 must be in {0,1} (prune on 2).  Window m:
    output positions [0, m) checked; positions [n, m) are the tail.

Layer 3 (full word): survivors of the windowed phase get their full tail
    [n, n + L) checked with the real 2^P (partial windows first, full only
    if partial passes).

Also: random-walk baseline (survival fraction of unconditioned inputs) to
separate 'carry automaton freedom' from 'constraint'.
"""
import sys, time, argparse
import numpy as np
from x2p_common import P, pow3, t_prefix, to_base3_bytes


def identity_checks():
    v15 = pow(2, P, pow3(15))
    v16 = pow(2, P, pow3(16))
    ok15 = (v15 == 1)
    ok16 = (v16 != 1)
    M = (pow(2, P) - 1) // pow3(15)
    # spot-check y = x + 3^15 M x for a random x
    x = 0xDEADBEEF123456789
    lhs = pow(2, P) * x
    rhs = x + pow3(15) * M * x
    print(f"[identity] 2^P = 1 mod 3^15: {ok15}   != 1 mod 3^16: {ok16}   "
          f"(v_3(2^P-1) = {15 if ok15 and ok16 else '??'})")
    print(f"[identity] y = x + 3^15*M*x spot check: {lhs == rhs}")
    print(f"[identity] 2^P mod 3 = {pow(2, P, 3)} (must be 1: N = 2^P == 1 mod 3)",
          flush=True)
    return ok15 and ok16 and lhs == rhs


class Search:
    def __init__(self, n, m, t, node_budget, cap_leaves):
        self.n, self.m = n, m
        self.t = np.asarray(t[:m], dtype=np.int64)
        self.f = np.zeros(m + 1, dtype=np.int64)
        self.budget = node_budget
        self.cap = cap_leaves
        self.nodes = 0
        self.max_depth = 0
        self.leaves = 0
        self.capped = False
        self.budget_hit = False
        self.survivors = []          # (word, rescues, max_chain)
        self.u = 0
        self.path = []
        self.rescues = 0
        self.chain = 0
        self.max_chain = 0

    def rec(self, i):
        self.nodes += 1
        if self.nodes > self.budget:
            self.budget_hit = True
            return
        if i > self.max_depth:
            self.max_depth = i
        if i == self.n:
            u = self.u
            for k in range(self.n, self.m):
                c = int(self.f[k])
                b = (c + u) % 3
                if b > 1:
                    return
                u = (c + u) // 3
            self.leaves += 1
            if len(self.survivors) < self.cap:
                self.survivors.append(
                    ("".join(map(str, self.path)), self.rescues, self.max_chain))
            return
        for a in (0, 1):
            c = int(self.f[i]) + a * int(self.t[0])
            u_in = self.u
            b = (c + u_in) % 3
            if b > 1:
                continue
            # rescue: raw digit wants 2 but carry-in flips it
            rescue = (c % 3 == 2) and u_in > 0
            if a:
                self.f[i + 1:self.m] += self.t[1:self.m - i]
            self.u = (c + u_in) // 3
            old_chain = self.chain
            if rescue:
                self.rescues += 1
                self.chain += 1
                if self.chain > self.max_chain:
                    self.max_chain = self.chain
            else:
                self.chain = 0
            self.path.append(a)
            self.rec(i + 1)
            self.path.pop()
            if rescue:
                self.rescues -= 1
            self.chain = old_chain
            self.u = u_in
            if a:
                self.f[i + 1:self.m] -= self.t[1:self.m - i]
            if self.budget_hit:
                return

    def run(self):
        t0 = time.time()
        self.rec(0)
        return time.time() - t0


def random_walks(n, m, t, walks, seed=7):
    rng = np.random.default_rng(seed)
    tt = np.asarray(t[:m], dtype=np.int64)
    surv = 0
    depths = np.zeros(walks, dtype=np.int64)
    for w in range(walks):
        f = np.zeros(m + 1, dtype=np.int64)
        u = 0
        i = 0
        while i < n:
            a = int(rng.integers(0, 2))
            c = int(f[i]) + a * int(tt[0])
            b = (c + u) % 3
            if b > 1:
                break
            if a:
                f[i + 1:m] += tt[1:m - i]
            u = (c + u) // 3
            i += 1
        if i == n:
            ok = True
            for k in range(n, m):
                c = int(f[k])
                b = (c + u) % 3
                if b > 1:
                    ok = False
                    break
                u = (c + u) // 3
            if ok:
                surv += 1
        depths[w] = i
    return surv, depths


def tail_window(x_int, n, W2):
    """Check output positions [n, n+W2) of 2^P*x for digit 2.
    Returns first position of 2 in window, or -1 if clean."""
    mod = pow3(n + W2)
    t = pow(2, P, mod)
    y = (t * x_int) % mod
    d = to_base3_bytes(y, n + W2)
    for k in range(n, n + W2):
        if d[k] == 2:
            return k
    return -1


def word_to_int(w):
    v = 0
    for ch in reversed(w):
        v = 3 * v + int(ch)
    return v


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--maxn", type=int, default=3000)
    ap.add_argument("--budget", type=int, default=3_000_000)
    ap.add_argument("--cap", type=int, default=5)
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()

    identity_checks()

    maxn = 1000 if args.quick else args.maxn
    t_pre = t_prefix(maxn + 8)
    print(f"[t] prefix {maxn+8} digits of 2^P built", flush=True)

    ladder = [50, 300] + ([] if args.quick else [1000, maxn])
    ladder = sorted(set(x for x in ladder if x <= maxn))

    print("\n=== Layer 2: windowed DFS (m = n, output fully committed) ===")
    results = []
    survivors_by_n = {}
    for n in ladder:
        budget = min(10_000_000, args.budget * (50 // max(n, 50) + 1)) \
            if n <= 300 else args.budget
        s = Search(n, n, t_pre, budget, args.cap)
        dt = s.run()
        print(f"n={n:<5} nodes={s.nodes:<9} max_depth={s.max_depth:<5} "
              f"leaves={s.leaves}{'+' if s.capped else ''} "
              f"budget_hit={s.budget_hit} survivors_kept={len(s.survivors)} "
              f"({dt:.1f}s)", flush=True)
        survivors_by_n[n] = s
        results.append(s)

    print("\n=== Random-walk baseline (unconditioned inputs) ===")
    for n in ladder:
        walks = 20000 if n <= 300 else (3000 if n <= 1000 else 500)
        surv, depths = random_walks(n, n, t_pre, walks)
        frac = surv / walks
        print(f"n={n:<5} walks={walks:<6} survive={surv:<6} frac={frac:.3e}  "
              f"mean_death_depth={depths.mean():.1f}  "
              f"(random-estimate (2/3)^n = {(2/3)**n:.3e})", flush=True)

    print("\n=== Survivor patterns (extendability records) ===")
    for n, s in survivors_by_n.items():
        for w, resc, ch in s.survivors[:3]:
            show = w if len(w) <= 120 else w[:60] + "..." + w[-60:]
            print(f"n={n} rescues={resc} max_rescue_chain={ch}  x={show}",
                  flush=True)

    print("\n=== Layer 3: full-word tail checks on survivors ===")
    W2s = [600, 3000]
    for n, s in survivors_by_n.items():
        if not s.survivors:
            continue
        for w, resc, ch in s.survivors[:3]:
            x = word_to_int(w)
            outs = []
            for W2 in W2s:
                if n + W2 > 14000:
                    continue
                f2 = tail_window(x, n, W2)
                outs.append(f"[n,n+{W2})={'CLEAN' if f2 < 0 else f'2 at {f2}'}")
            print(f"n={n} x={w[:40]}...  " + "  ".join(outs), flush=True)
            if outs and all('CLEAN' in o for o in outs):
                y = pow(2, P) * x
                L = 0
                vv = y
                while vv:
                    vv //= 3
                    L += 1
                d = to_base3_bytes(y, L)
                pos = next((i for i, v in enumerate(d) if v == 2), -1)
                print(f"  FULL WORD: len={L} first2={pos}", flush=True)

    print("\n=== Window m=301 (R2 window origin), depth ladder ===")
    t301 = t_prefix(301)
    for n in [150, 286, 301]:
        s = Search(n, 301, t301, args.budget, args.cap)
        dt = s.run()
        print(f"n={n:<4} m=301 nodes={s.nodes:<9} max_depth={s.max_depth:<5} "
              f"leaves={s.leaves}{'+' if s.capped else ''} "
              f"budget_hit={s.budget_hit} ({dt:.1f}s)", flush=True)
        for w, resc, ch in s.survivors[:2]:
            print(f"     survivor: x={w} rescues={resc} chain={ch}", flush=True)


if __name__ == "__main__":
    main()
