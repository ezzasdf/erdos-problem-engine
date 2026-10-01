#!/usr/bin/env python3
"""
Computational investigation of the N_K → N_{K+1} lifting structure.
Optimized version: run in stages, skip K=17 initially.
"""

from collections import defaultdict
import sys
import time

def pow2_mod(r, m):
    return pow(2, r, m)

def has_trailing_digit_2(val, K):
    v = val
    for _ in range(K):
        if v % 3 == 2:
            return True
        v //= 3
    return False

def uk(K):
    if K <= 0: return 1
    return 2 * (3 ** (K - 1))

def compute_nk(K):
    period = uk(K)
    modulus = 3 ** K
    result = []
    for r in range(period):
        p = pow2_mod(r, modulus)
        if not has_trailing_digit_2(p, K):
            result.append(r)
    return set(result)

def stage1_basic_stats(nk):
    print("="*80)
    print("STAGE 1: Basic N_K Statistics")
    print("="*80)
    special = {0, 2, 8}
    for K in sorted(nk.keys()):
        in_special = special & nk[K]
        missing = special - nk[K]
        print(f"K={K:2d}: |N_K|={len(nk[K]):6d}  uK={uk(K):>12d}  "
              f"{{0,2,8}}⊂N_K: {'YES' if not missing else 'NO'} missing={sorted(missing)}")

def stage2_transition_patterns(nk):
    print("\n" + "="*80)
    print("STAGE 2: Lifting Transition Patterns (r → {r, r+u_K, r+2u_K})")
    print("="*80)
    
    for K in sorted(nk.keys()):
        if K+1 not in nk:
            continue
        period_k = uk(K)
        nk_k = nk[K]
        nk_k1 = nk[K + 1]
        
        patterns = defaultdict(list)
        for r in sorted(nk_k):
            lifts = [
                (0, r),
                (1, r + period_k),
                (2, r + 2 * period_k),
            ]
            survival = tuple(idx for idx, (s, lr) in enumerate(lifts) if lr in nk_k1)
            patterns[survival].append(r)
        
        print(f"\n--- K={K} → K={K+1} ---")
        print(f"|N_K|={len(nk_k):5d}, |N_{{K+1}}|={len(nk_k1):5d}")
        
        # Compute how many elements of N_{K+1} are covered
        all_lifts = set()
        for r in nk_k:
            all_lifts.add(r)
            all_lifts.add(r + period_k)
            all_lifts.add(r + 2 * period_k)
        covered = all_lifts & nk_k1
        uncovered = nk_k1 - all_lifts
        
        for pattern in sorted(patterns.keys()):
            count = len(patterns[pattern])
            label = ",".join(str(p) for p in pattern) if pattern else "DEAD"
            pct = 100 * count / len(nk_k) if nk_k else 0
            print(f"  lifts({{{label}}}): {count:5d} ({pct:5.1f}%)")
        
        print(f"  Coverage: {len(covered):5d}/{len(nk_k1):5d} elements of N_{{K+1}} covered by lifts")
        print(f"  Uncovered: {len(uncovered):5d}", end="")
        if uncovered and len(uncovered) <= 10:
            print(f"  {sorted(uncovered)}")
        else:
            print()

def stage3_survival_rates(nk):
    print("\n" + "="*80)
    print("STAGE 3: Survival Rates of Non-Special Elements")
    print("="*80)
    special = {0, 2, 8}
    
    for K in sorted(nk.keys()):
        if K+1 not in nk:
            continue
        period_k = uk(K)
        nk_k = nk[K]
        nk_k1 = nk[K + 1]
        non_special = nk_k - special
        
        if not non_special:
            print(f"K={K:2d}: no non-special elements")
            continue
        
        base_surv = sum(1 for r in non_special if r in nk_k1)
        shift1_surv = sum(1 for r in non_special if (r + period_k) in nk_k1)
        shift2_surv = sum(1 for r in non_special if (r + 2 * period_k) in nk_k1)
        
        # How many distinct N_{K+1} elements do non-special lifts produce?
        lift_set = set()
        for r in non_special:
            lift_set.add(r)
            lift_set.add(r + period_k)
            lift_set.add(r + 2 * period_k)
        surviving = lift_set & nk_k1
        
        print(f"K={K:2d}→{K+1}: |NS|={len(non_special):5d}  "
              f"base→{base_surv:4d}  +u→{shift1_surv:4d}  +2u→{shift2_surv:4d}  "
              f"distinct in N_{{K+1}}: {len(surviving):5d}")

def stage4_transition_graph(nk):
    print("\n" + "="*80)
    print("STAGE 4: Transition Graph Summary")
    print("="*80)
    
    for K in sorted(nk.keys()):
        if K+1 not in nk:
            continue
        period_k = uk(K)
        nk_k = nk[K]
        nk_k1 = nk[K + 1]
        
        dead = one = two = three = 0
        one_details = defaultdict(int)
        
        for r in nk_k:
            s = [
                r in nk_k1,
                (r + period_k) in nk_k1,
                (r + 2 * period_k) in nk_k1,
            ]
            n = sum(s)
            if n == 0: dead += 1
            elif n == 1:
                one += 1
                for i, v in enumerate(s):
                    if v: one_details[i] += 1
            elif n == 2: two += 1
            else: three += 1
        
        total = len(nk_k)
        d = 100*dead/total if total else 0
        print(f"K={K:2d}→{K+1:2d}: |N|={total:5d}  "
              f"dead={dead:4d}({d:5.1f}%)  "
              f"1={one:4d}(base={one_details.get(0,0)} +u={one_details.get(1,0)} +2u={one_details.get(2,0)})  "
              f"2={two:4d}  3={three:4d}")

def stage5_special_lifting(nk):
    print("\n" + "="*80)
    print("STAGE 5: How do {0, 2, 8} lift through the levels?")
    print("="*80)
    
    special = {0, 2, 8}
    for K in sorted(nk.keys()):
        if K+1 not in nk:
            continue
        period_k = uk(K)
        nk_k1 = nk[K + 1]
        
        print(f"\nK={K} → K={K+1} (uK={period_k}):")
        for s in sorted(special):
            if s not in nk[K]:
                print(f"  r={s}: NOT in N_{K}")
                continue
            lifts = [
                (f"{s}", s),
                (f"{s}+{period_k}", s + period_k),
                (f"{s}+2·{period_k}", s + 2 * period_k),
            ]
            for label, lr in lifts:
                status = "IN N" if lr in nk_k1 else "NOT in N"
                print(f"  r={s}: lift {label:20s} = {lr:>12d}  →  {status}  (mod uK_{'%d'%(K+1)} = {lr % uk(K+1)})")

def stage6_residue_analysis(nk):
    """Analyze N_K elements modulo uK to find structural patterns."""
    print("\n" + "="*80)
    print("STAGE 6: Residue Analysis — N_K mod small numbers")
    print("="*80)
    
    for K in sorted(nk.keys()):
        nk_k = nk[K]
        # Residues mod 3
        mod3 = defaultdict(int)
        for r in nk_k:
            mod3[r % 3] += 1
        print(f"K={K:2d}: |N|={len(nk_k):5d}  mod 3: {dict(sorted(mod3.items()))}", end="")
        
        # Check if all elements ≡ 0 mod 3 (except possibly 2)
        # Actually let's check what fraction are ≡ 0, 1, 2 mod 3
        total = len(nk_k)
        for d in [0, 1, 2]:
            cnt = mod3.get(d, 0)
            if cnt > 0:
                print(f"  {d}→{cnt}({100*cnt/total:.1f}%)", end="")
        print()


if __name__ == "__main__":
    # Stage 0: Compute N_K for K=5..16 (skip 17 for now)
    max_K = 16
    print(f"Computing N_K for K=5..{max_K}...")
    sys.stdout.flush()
    
    nk = {}
    for K in range(5, max_K + 1):
        t0 = time.time()
        nk[K] = compute_nk(K)
        t1 = time.time()
        print(f"  K={K}: |N_K|={len(nk[K]):6d}  uK={uk(K):>12d}  ({t1-t0:.1f}s)")
        sys.stdout.flush()
    
    # Also compute N_{17} if feasible (uK=86M, might be slow)
    if max_K >= 16:
        print(f"\n  Computing K=17 (uK={uk(17)} = 86M elements)... (may take a while)")
        sys.stdout.flush()
        t0 = time.time()
        nk[17] = compute_nk(17)
        t1 = time.time()
        print(f"  K=17: |N_17|={len(nk[17]):6d}  ({t1-t0:.1f}s)")
        sys.stdout.flush()
    
    stage1_basic_stats(nk)
    stage2_transition_patterns(nk)
    stage3_survival_rates(nk)
    stage4_transition_graph(nk)
    stage5_special_lifting(nk)
    stage6_residue_analysis(nk)
    
    print("\n" + "="*80)
    print("ANALYSIS COMPLETE")
    print("="*80)
